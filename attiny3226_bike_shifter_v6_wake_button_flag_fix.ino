/*
  ATtiny3226 BIKE SHIFTER - ideal gear positions + temporary overshift
  Non-latching motor timeout; interrupt-captured button taps; quick deep sleep.
  V3 button-capture kept intact; serial RX (PB3) can wake to calibrate.
  V5: PB3 only OPENS a 6-second serial confirmation window, not calibration.
  V6: clear stale awake-button wake latches to prevent missed first reverse
      shift when waking at gear 1 (UP) or gear 6 (DOWN).
  Send "xx" (any character TWICE) while in that window to enter
  indefinite calibration. This rejects random PB3 edges/serial line noise.
  Unconfirmed serial wake automatically returns to sleep. Button wakes
  never enter calibration. Encoder jitter cannot postpone idle sleep.
  Z1 saves pending changes then restores automatic sleep.
  Based on the user's working PC2 / PA2 / PA4 low-current sketch.

  megaTinyCore 2.6.11 / ATtiny3226 / internal 8 MHz / 115200 baud.
  PA3 DRV IN1, PA5 DRV IN2, PA6 DRV nSLEEP.
  PA4 powers AS5600 (sensor breakout already verified on battery voltage).
  PB0 AS5600 SCL, PB1 SDA; pull-ups to switched PA4, NOT battery+.
  PB2 serial TX, PB3 serial RX; PC2 gear + (1->2), PA2 gear - (2->1).

  ONE IDEAL POSITION per gear. Each shift can overshoot the ideal position
  by a specified number of AS5600 counts in its direction of travel, pause
  briefly, and return to the ideal running position.

  EEPROM: new v2 data stored at address 64, leaving your PREVIOUS v1
  EEPROM calibration untouched at address 0. On first use, imports old
  C1-/C2+/C2-/.../C6+ positions into six ideal starting positions.
  Does not write EEPROM until W. V2 is preferred on subsequent startups.

  Commands (Serial Monitor 115200):
    L        list ideal positions, overshifts, settings
    0..4095  manual encoder target
    +N / -N  manually jog target +/- counts
    T        motor off, copy RAW to TARGET; does NOT write EEPROM
    C2       store current TARGET as gear 2's IDEAL position in RAM
    O2+30    overshift 30 counts when ARRIVING at gear 2 from gear 1
    O2-30    overshift 30 counts when ARRIVING at gear 2 from gear 3
    F230     full-power shift PWM (range 100..255)
    H180     return-to-ideal PWM (range 80..255)
    G1..G6   declare currently selected gear; no movement
    > / <    shift toward gear 6 / toward gear 1
    s        STOP MOTOR, no fault latch; next button still works
    xx       send after PB3 wakes: same character twice confirms calibration
    Z0       keep awake for calibration (legacy)
    Z1       save calibration and re-enable auto sleep
    Z        request sleep now if motor idle
    W        save V2 table and settings to EEPROM (old V1 remains)
    E        reload EEPROM without moving
    p        show status; ? help
    r        reverse motor polarity (requires W to save)
    dNN kNN bNN uNN vNN   original manual PD controller settings

  Important: A motor timeout stops power but NEVER blocks the buttons.
  Requested gear and encoder-aligned gear are tracked separately. Encoder
  alignment does NOT prove that the chain actually engaged the sprocket.
  If a shift times out, selecting another gear still works immediately.
  Shift + / - directions refer to GEAR NUMBER, not speed nomenclature.

  CAUTION: Configure overshift values on a stand, with pedals turning and
  derailleur clear of its mechanical limits. O2+/O2- can be set to 0.
  No uncommanded movement at power-on. EEPROM preserved across UPDI upload
  only when the EESAVE fuse is configured appropriately.
*/

#include <Arduino.h>
#include <Wire.h>
#include <EEPROM.h>
#include <stdlib.h>
#include <stddef.h>
#include <avr/sleep.h>
#include <avr/interrupt.h>

const uint8_t SENSOR = 0x36;
const uint8_t IN1=PIN_PA3, IN2=PIN_PA5, NSLEEP=PIN_PA6;
const uint8_t SENSOR_POWER=PIN_PA4;
const uint8_t BUTTON_PLUS=PIN_PC2, BUTTON_MINUS=PIN_PA2;
const uint8_t GEAR_COUNT=6;
const uint16_t UNSET=0xFFFF;
const uint8_t FROM_LOWER=0, FROM_HIGHER=1;
const uint16_t OLD_MAGIC=0xB426, NEW_MAGIC=0xB427;
const uint8_t OLD_VERSION=1, NEW_VERSION=2;
const int NEW_EEPROM_ADDR=64;

const unsigned long DEBOUNCE_MS=35, SENSOR_START_MS=20;
const unsigned long NO_MOTION_TIMEOUT_MS=550; // motor energized, encoder not moving
const unsigned long STAGE_TIMEOUT_MS=1600;     // max per leg even if creeping
const unsigned long COMPLETE_HOLD_MS=300;     // let chain catch overshift
const unsigned long SLEEP_IDLE_MS=500;        // 0.5s after settled/timeout
const unsigned long BOOT_SERIAL_GRACE_MS=3000; // serial entry grace on boot
const unsigned long WAKE_RX_DRAIN_MS=200; // discard buffered wake bytes
const unsigned long SERIAL_CONFIRM_MS=6000; // no confirmed chars => sleep
const uint8_t SERIAL_CONFIRM_CHARS=2;      // two identical printable bytes
const int OVERSHIFT_TOL=12, FINAL_TOL=18;
const int BOOT_GEAR_TOL=35, BOOT_GEAR_MARGIN=22;
const int BOOT_RECOVERY_MAX_DIST=150; // allows navigation after reset mid-shift

// Existing PD parameters retained for manual serial-position control.
int deadband=20, kp100=50, kd=6, pwmMin=160, pwmMax=200;
bool reversePolarity=true;
int fastPwm=230, returnPwm=185; // shift behavior independent of manual PD
uint16_t ideal[GEAR_COUNT];
uint8_t overshift[GEAR_COUNT][2];
bool unsavedChanges=false;
bool importedOld=false;
bool forceSleepRequested=false;

int raw=0, oldRaw=0, target=0;
long velocityQ8=0;
int appliedPWM=0, appliedDir=0;
bool sensorOK=false, sensorPowerOn=false, autoSleep=true;
// Serial may enter calibration while awake ONLY during the initial boot
// grace window; never re-enable this after a button wake or after Z1.
bool bootSerialEntryEnabled=true;
// PB3 is a wake *request*; it is NOT evidence of intentional calibration.
// Serial confirmation is time-limited; only deliberate input changes mode.
bool serialWakePending=false;
unsigned long serialConfirmDeadline=0;
uint8_t serialConfirmChars=0;
char serialConfirmFirst=0;
uint32_t serialConfirmTimeouts=0;
// For diagnostics: record sleep-wake sources.
uint32_t buttonWakes=0, serialWakes=0, unknownWakes=0;
bool halfTurnLock=false;
int halfTurnDir=1;
uint8_t selectedGear=0, alignedGear=0; // 0 = unknown/not aligned

// One shift transaction: target to OVERSHIFT, brief brake, return to IDEAL.
enum Phase : uint8_t { IDLE=0, TO_OVERSHIFT=1, OVERSHIFT_HOLD=2,
                       RETURN_IDEAL=3, MANUAL_MOVE=4 };
Phase phase=IDLE;
unsigned long phaseStart=0, lastMovement=0, lastActivity=0;
unsigned long lastReport=0, lastControl=0, lastEncoderChange=0, bootGraceEnd=0;
int movementRaw=0, legDirection=0, finalIdeal=0;
uint8_t movingToGear=0;

char command[28];
uint8_t commandLength=0;
unsigned long lastByte=0;
// Capture short presses whether awake OR asleep.  An interrupt sets a bit;
// the main loop consumes it, avoiding missed pulses during the 500 ms awake
// window.  Interrupts only latch events; they never run motor control.
volatile uint8_t wakeButtons=0;
volatile uint8_t buttonEdges=0;
volatile bool wakeSerial=false;
void wakeSerialISR() { wakeSerial=true; }
void wakePlusISR() {
  if (digitalRead(BUTTON_PLUS)==LOW) { wakeButtons|=1; buttonEdges|=1; }
}
void wakeMinusISR() {
  if (digitalRead(BUTTON_MINUS)==LOW) { wakeButtons|=2; buttonEdges|=2; }
}
// A button cannot generate another shift until it has been released for
// DEBOUNCE_MS.  This suppresses contact bounce but captures short taps.
bool plusArmed=true, minusArmed=true;
unsigned long plusHighSince=0, minusHighSince=0;
unsigned long acceptedPlus=0, acceptedMinus=0;
void updateRearm(bool &armed, unsigned long &highSince, uint8_t pin,
                 unsigned long now) {
  if (armed) return;
  if (digitalRead(pin)==LOW) { highSince=0; return; }
  if (!highSince) highSince=now;
  if (now-highSince>=DEBOUNCE_MS) armed=true;
}

struct DebouncedButton {
  uint8_t pin;
  bool lastReading;
  bool stable;
  unsigned long changedAt;
};
DebouncedButton plusButton, minusButton;

// EXACT legacy EEPROM layout from the last working firmware.
struct OldConfig {
  uint16_t magic;
  uint8_t version;
  uint16_t gears[GEAR_COUNT][2];
  uint16_t db;
  uint16_t kp;
  uint8_t damping;
  uint8_t minPwm;
  uint8_t maxPwm;
  uint8_t reversed;
  uint16_t crc;
};

// V2 lives at EEPROM address 64. Old address 0 is NEVER overwritten.
struct NewConfig {
  uint16_t magic;
  uint8_t version;
  uint16_t ideal[GEAR_COUNT];
  uint8_t overshift[GEAR_COUNT][2];
  uint16_t db;
  uint16_t kp;
  uint8_t damping;
  uint8_t minPwm;
  uint8_t maxPwm;
  uint8_t reversed;
  uint8_t fastPwm;
  uint8_t returnPwm;
  uint16_t crc;
};

// Explicit declarations after struct definitions avoid Arduino auto-prototype
// errors: 'OldConfig' / 'DebouncedButton' does not name a type.
uint16_t oldChecksum(const OldConfig &s);
uint16_t newChecksum(const NewConfig &s);
bool validOld(const OldConfig &s);
bool validNew(const NewConfig &s);
void fillNew(NewConfig &s);
void initButton(DebouncedButton &button, uint8_t pin);
bool pressEvent(DebouncedButton &button, unsigned long now);

int wrapped(int x) {
  if (x>2047) x-=4096;
  if (x< -2048) x+=4096;
  return x;
}
uint16_t wrapTarget(long t) {
  t%=4096;
  if (t<0) t+=4096;
  return (uint16_t)t;
}

bool readAngle(int &value) {
  Wire.beginTransmission(SENSOR);
  Wire.write((uint8_t)0x0C);
  if (Wire.endTransmission(false)!=0) return false;
  if (Wire.requestFrom(SENSOR,(uint8_t)2)!=2) return false;
  int hi=Wire.read(),lo=Wire.read();
  if (hi<0 || lo<0) return false;
  value=((hi&15)<<8)|lo;
  return true;
}
void sensorPowerUp() {
  digitalWrite(SENSOR_POWER,HIGH);
  delay(SENSOR_START_MS);
  Wire.begin(); Wire.setClock(100000);
  sensorPowerOn=true;
}
void sensorPowerDown() {
  Wire.end();
  pinMode(PIN_PB0,INPUT);
  pinMode(PIN_PB1,INPUT);
  digitalWrite(SENSOR_POWER,LOW);
  sensorPowerOn=false;
  sensorOK=false;
}
void motorOff() {
  analogWrite(IN1,0);
  analogWrite(IN2,0);
  digitalWrite(NSLEEP,LOW);
  appliedPWM=0; appliedDir=0;
}
void motorBrake() {
  digitalWrite(NSLEEP,HIGH);
  analogWrite(IN1,255);
  analogWrite(IN2,255);
  appliedPWM=0; appliedDir=0;
}
void motorDrive(int dir, int pwm) {
  int physicalDir=reversePolarity ? -dir : dir;
  digitalWrite(NSLEEP,HIGH);
  if (physicalDir>0) {
    analogWrite(IN2,0);
    analogWrite(IN1,pwm);
  } else {
    analogWrite(IN1,0);
    analogWrite(IN2,pwm);
  }
  appliedPWM=pwm; appliedDir=dir;
}

// Retain antipode protection from original good shifter code.
int controlError() {
  int e=wrapped(target-raw);
  int mag=abs(e);
  if (!halfTurnLock && mag>=1900) {
    if (mag==2048 && abs(velocityQ8)>=512)
      halfTurnDir=velocityQ8>0 ? 1 : -1;
    else halfTurnDir=e>=0 ? 1 : -1;
    halfTurnLock=true;
  }
  if (halfTurnLock) {
    if (mag>1600) return halfTurnDir*mag;
    halfTurnLock=false;
  }
  return e;
}

uint16_t crcBytes(const uint8_t *bytes, size_t len) {
  uint16_t crc=0xFFFF;
  for (size_t i=0;i<len;i++) {
    crc ^= (uint16_t)bytes[i]<<8;
    for (uint8_t bit=0;bit<8;bit++)
      crc=(crc&0x8000) ? (uint16_t)((crc<<1)^0x1021) : (uint16_t)(crc<<1);
  }
  return crc;
}
uint16_t oldChecksum(const OldConfig &s) {
  return crcBytes((const uint8_t*)&s,offsetof(OldConfig,crc));
}
uint16_t newChecksum(const NewConfig &s) {
  return crcBytes((const uint8_t*)&s,offsetof(NewConfig,crc));
}
bool validOld(const OldConfig &s) {
  if (s.magic!=OLD_MAGIC || s.version!=OLD_VERSION || s.crc!=oldChecksum(s)) return false;
  if (s.db<1 || s.db>500 || s.kp<1 || s.kp>150 || s.damping>30) return false;
  if (s.minPwm>250 || s.maxPwm<1 || s.minPwm>s.maxPwm || s.reversed>1) return false;
  for (uint8_t g=0;g<GEAR_COUNT;g++)
    for (uint8_t d=0;d<2;d++)
      if (s.gears[g][d]!=UNSET && s.gears[g][d]>4095) return false;
  return true;
}
bool validNew(const NewConfig &s) {
  if (s.magic!=NEW_MAGIC || s.version!=NEW_VERSION || s.crc!=newChecksum(s)) return false;
  if (s.db<1 || s.db>500 || s.kp<1 || s.kp>150 || s.damping>30) return false;
  if (s.minPwm>250 || s.maxPwm<1 || s.minPwm>s.maxPwm || s.reversed>1) return false;
  if (s.fastPwm<100 || s.returnPwm<80) return false;
  for (uint8_t g=0;g<GEAR_COUNT;g++) {
    if (s.ideal[g]!=UNSET && s.ideal[g]>4095) return false;
    if (s.overshift[g][0]>80 || s.overshift[g][1]>80) return false;
  }
  return true;
}
void setDefaultTable() {
  for (uint8_t g=0;g<GEAR_COUNT;g++) {
    ideal[g]=UNSET;
    // Start conservatively: 20 counts on interior gears; ZERO at cassette ends.
    overshift[g][0]=(g>0 && g<5)?20:0;
    overshift[g][1]=(g>0 && g<5)?20:0;
  }
  importedOld=false;
}
void fillNew(NewConfig &s) {
  s=NewConfig(); // initialize before CRC (AVR struct layout)
  s.magic=NEW_MAGIC; s.version=NEW_VERSION;
  for (uint8_t g=0;g<GEAR_COUNT;g++) {
    s.ideal[g]=ideal[g];
    s.overshift[g][0]=overshift[g][0];
    s.overshift[g][1]=overshift[g][1];
  }
  s.db=deadband; s.kp=kp100; s.damping=kd;
  s.minPwm=pwmMin; s.maxPwm=pwmMax;
  s.reversed=reversePolarity?1:0;
  s.fastPwm=fastPwm; s.returnPwm=returnPwm;
  s.crc=newChecksum(s);
}

// A gear's average of two old directional targets is a STARTING POINT ONLY.
// Use shortest wrapped difference so crossing 0/4095 is handled correctly.
uint16_t importedIdeal(uint16_t a, uint16_t b) {
  if (a==UNSET) return b;
  if (b==UNSET) return a;
  return wrapTarget((long)a + wrapped((int)b-(int)a)/2);
}
bool loadConfig() {
  NewConfig next;
  EEPROM.get(NEW_EEPROM_ADDR,next);
  if (validNew(next)) {
    for (uint8_t g=0;g<GEAR_COUNT;g++) {
      ideal[g]=next.ideal[g];
      for (uint8_t d=0;d<2;d++) overshift[g][d]=next.overshift[g][d];
    }
    deadband=next.db; kp100=next.kp; kd=next.damping;
    pwmMin=next.minPwm; pwmMax=next.maxPwm;
    reversePolarity=next.reversed;
    fastPwm=next.fastPwm; returnPwm=next.returnPwm;
    importedOld=false; unsavedChanges=false;
    Serial.println(F("EEPROM V2: ideal positions + overshifts loaded."));
    return true;
  }
  OldConfig previous;
  EEPROM.get(0,previous);
  if (validOld(previous)) {
    for (uint8_t g=0;g<GEAR_COUNT;g++) {
      ideal[g]=importedIdeal(previous.gears[g][FROM_LOWER], previous.gears[g][FROM_HIGHER]);
    }
    deadband=previous.db; kp100=previous.kp; kd=previous.damping;
    pwmMin=previous.minPwm; pwmMax=previous.maxPwm;
    reversePolarity=previous.reversed;
    importedOld=true;
    unsavedChanges=true;  // imported values not yet saved in new V2 slot
    Serial.println(F("EEPROM V1 imported into RAM. L to inspect, W to save V2."));
    Serial.println(F("Original EEPROM V1 remains unchanged at address 0."));
    return true;
  }
  Serial.println(F("No valid V1 or V2 gear table; calibrate with C1..C6."));
  return false;
}
void stopMotion() {
  phase=IDLE;
  movingToGear=0;
  motorOff();
}
void saveConfig() {
  stopMotion();
  NewConfig next;
  fillNew(next);
  EEPROM.put(NEW_EEPROM_ADDR,next);
  NewConfig verify;
  EEPROM.get(NEW_EEPROM_ADDR,verify);
  if (validNew(verify)) {
    unsavedChanges=false;
    importedOld=false;
    Serial.println(F("EEPROM V2 SAVED AND VERIFIED; original V1 untouched."));
  } else Serial.println(F("ERROR: V2 EEPROM verify failed."));
}
void printTable() {
  Serial.println(F("Gear  IDEAL   overshift + (from lower)   overshift - (from higher)"));
  for (uint8_t g=0;g<GEAR_COUNT;g++) {
    Serial.print(g+1); Serial.print(F("     "));
    if (ideal[g]==UNSET) Serial.print(F("---")); else Serial.print(ideal[g]);
    Serial.print(F("        ")); Serial.print(overshift[g][0]);
    Serial.print(F("                       ")); Serial.println(overshift[g][1]);
  }
  Serial.print(F("F="));Serial.print(fastPwm);
  Serial.print(F(" H="));Serial.print(returnPwm);
  Serial.print(F(" d="));Serial.print(deadband);
  Serial.print(F(" k="));Serial.print(kp100);
  Serial.print(F(" b="));Serial.print(kd);
  Serial.print(F(" u="));Serial.print(pwmMin);
  Serial.print(F(" v="));Serial.print(pwmMax);
  Serial.print(F(" REV="));Serial.println(reversePolarity?1:0);
  Serial.print(F("unsaved="));Serial.print(unsavedChanges?F("YES"):F("NO"));
  Serial.print(F(" imported_V1="));Serial.println(importedOld?F("YES"):F("NO"));
}

void inferGear() {
  selectedGear=alignedGear=0;
  if (!sensorOK) return;
  int best=4096, runner=4096;
  uint8_t bestGear=0;
  for (uint8_t g=0;g<GEAR_COUNT;g++) {
    if (ideal[g]==UNSET) continue;
    int distance=abs(wrapped((int)ideal[g]-raw));
    if (distance<best) { runner=best;best=distance;bestGear=g+1; }
    else if (distance<runner) runner=distance;
  }
  // If power was cycled halfway through a shift, prefer a best-effort
  // nearest requested gear over locking out the handlebar controls.
  // It is a navigation reference ONLY, not proof the chain is engaged.
  if (best<=BOOT_RECOVERY_MAX_DIST) selectedGear=bestGear;
  if (best<=BOOT_GEAR_TOL && runner-best>=BOOT_GEAR_MARGIN)
    alignedGear=bestGear;
}
void showStatus() {
  Serial.print(F("RAW="));Serial.print(raw);
  Serial.print(F(" TARGET="));Serial.print(target);
  Serial.print(F(" ERR="));Serial.print(wrapped(target-raw));
  Serial.print(F(" PWM="));Serial.print(appliedPWM);
  Serial.print(F(" DIR="));Serial.print(appliedDir);
  Serial.print(F(" SELECTED=")); if(selectedGear) Serial.print(selectedGear);else Serial.print('?');
  Serial.print(F(" AT_GEAR=")); if(alignedGear) Serial.print(alignedGear);else Serial.print('?');
  Serial.print(F(" PHASE="));
  switch (phase) {
    case IDLE: Serial.print(F("IDLE"));break;
    case TO_OVERSHIFT: Serial.print(F("OVER"));break;
    case OVERSHIFT_HOLD: Serial.print(F("HOLD"));break;
    case RETURN_IDEAL: Serial.print(F("RETURN"));break;
    case MANUAL_MOVE: Serial.print(F("MANUAL"));break;
  }
  Serial.print(F(" SENSOR="));Serial.print(sensorOK?F("OK"):F("ERR"));
  Serial.print(F(" AUTO_SLEEP="));Serial.print(autoSleep?1:0);
  Serial.print(F(" BOOT_SERIAL="));Serial.print(bootSerialEntryEnabled?1:0);
  Serial.print(F(" W_BUTTON="));Serial.print(buttonWakes);
  Serial.print(F(" W_SERIAL="));Serial.print(serialWakes);
  Serial.print(F(" W_OTHER="));Serial.print(unknownWakes);
  Serial.print(F(" SERIAL_PENDING="));Serial.print(serialWakePending?1:0);
  Serial.print(F(" RX_TIMEOUT="));Serial.print(serialConfirmTimeouts);
  Serial.print(F(" SLEEP_BLOCK="));
  if (!autoSleep) Serial.print(F("CALIBRATION"));
  else if (serialWakePending) Serial.print(F("RX_CONFIRM"));
  else if (phase!=IDLE) Serial.print(F("SHIFT"));
  else if (commandLength) Serial.print(F("COMMAND"));
  else if (digitalRead(BUTTON_PLUS)==LOW || digitalRead(BUTTON_MINUS)==LOW)
    Serial.print(F("BUTTON_HELD"));
  else if (millis()<bootGraceEnd) Serial.print(F("BOOT_GRACE"));
  else if (millis()-lastActivity < SLEEP_IDLE_MS) Serial.print(F("IDLE_TIMER"));
  else Serial.print(F("NONE"));
  Serial.print(F(" BTN_PLUS="));Serial.print(acceptedPlus);
  Serial.print(F(" BTN_MINUS="));Serial.println(acceptedMinus);
}
void help() {
  Serial.println(F("0..4095 target | +/-N jog | T set TARGET=RAW (motor off)"));
  Serial.println(F("C2 save ideal gear 2 | O2+30 / O2-30 set overshift by arrival direction"));
  Serial.println(F("L list | W save V2 EEPROM | E reload | G1..G6 assume selected gear"));
  Serial.println(F("> toward gear 6 | < toward gear 1 | p status | s stop | ? help"));
  Serial.println(F("F230 fast PWM | H185 return PWM | r reverse polarity"));
  Serial.println(F("From sleep, send a burst to wake PB3, then send xx within 6 seconds."));
  Serial.println(F("Send the SAME printable character twice (xx) to confirm; random edges will time out."));
  Serial.println(F("After button wake, serial bytes are discarded (no accidental calibration)."));
  Serial.println(F("Z0 stay awake | Z1 SAVE + exit calibration | Z sleep now"));
  Serial.println(F("After Z1, sleep resumes. Repeat wake burst then xx to calibrate."));
  Serial.println(F("Button interrupts stay enabled awake and asleep; p shows BTN_PLUS/MINUS counts."));
  Serial.println(F("No latched faults; after timeout either button may request a shift."));
}

void resetLeg(unsigned long now) {
  phaseStart=lastMovement=now;
  movementRaw=raw;
  legDirection=0;
  halfTurnLock=false;
  oldRaw=raw;
  velocityQ8=0;
}
void terminateMove(const __FlashStringHelper *reason) {
  motorOff();
  phase=IDLE;
  movingToGear=0;
  alignedGear=0; // motor did not reach the requested position
  lastActivity=millis();
  Serial.print(F("STOP (no lockout): ")); Serial.println(reason);
  Serial.println(F("Press either button for another attempt or opposite gear."));
}
void beginManual(uint16_t pos) {
  if (!sensorOK) {
    Serial.println(F("No AS5600 reading; manual target rejected."));
    return;
  }
  target=pos;
  phase=MANUAL_MOVE; movingToGear=0;
  selectedGear=alignedGear=0;
  resetLeg(millis());
  lastActivity=millis();
  Serial.print(F("MANUAL TARGET="));Serial.println(target);
}

// When moving in a direction, compute temporary overshoot beyond the
// IDEAL gear target in that SAME direction. Never assume encoder sign.
void shiftGear(int change) {
  if (!sensorOK) {
    Serial.println(F("Sensor unavailable; no drive. Try another button after recovery."));
    stopMotion(); return;
  }
  if (!selectedGear) {
    Serial.println(F("Gear unknown. Use G1..G6 to identify physical gear (no movement)."));
    return;
  }
  int next=(int)selectedGear+change;
  if (next<1 || next>GEAR_COUNT) {
    Serial.println(F("End gear reached; opposite direction remains available."));
    return;
  }
  if (ideal[next-1]==UNSET || ideal[selectedGear-1]==UNSET) {
    Serial.println(F("Gear position missing. Use L and Cn for calibration."));
    return;
  }
  uint8_t arriving=change>0 ? FROM_LOWER : FROM_HIGHER;
  int delta=wrapped((int)ideal[next-1]-(int)ideal[selectedGear-1]);
  if (delta==0) {
    Serial.println(F("Adjacent ideal positions identical; check table."));
    return;
  }
  int sign=delta>0?1:-1;
  int extra=overshift[next-1][arriving];
  finalIdeal=ideal[next-1];
  target=wrapTarget((long)finalIdeal+sign*extra);
  selectedGear=(uint8_t)next; // desired gear, NOT confirmation
  alignedGear=0;
  movingToGear=selectedGear;
  phase=TO_OVERSHIFT;
  resetLeg(millis());
  lastActivity=millis();
  Serial.print(F("SHIFT toward gear "));Serial.print(selectedGear);
  Serial.print(F(" OVER="));Serial.print(target);
  Serial.print(F(" IDEAL="));Serial.println(finalIdeal);
}

bool parseInteger(const char *str, long &result) {
  if (!*str) return false;
  char *end;
  result=strtol(str,&end,10);
  return end!=str && *end=='\0';
}
void captureTarget() {
  stopMotion();
  int a;
  if (!sensorPowerOn || !readAngle(a)) {
    Serial.println(F("T failed: encoder not responding."));return;
  }
  raw=oldRaw=target=a;
  sensorOK=true;
  alignedGear=selectedGear=0;
  lastActivity=millis();
  Serial.print(F("T: RAW copied to TARGET="));Serial.println(target);
  Serial.println(F("No EEPROM change. C# stores ideal in RAM; W writes EEPROM."));
}
void runCommand() {
  if (!commandLength) return;
  command[commandLength]='\0';
  commandLength=0;
  char c=command[0];
  long value;
  if (c>='0' && c<='9') {
    if (!parseInteger(command,value)||value<0||value>4095)
      Serial.println(F("Position must be 0..4095"));
    else beginManual((uint16_t)value);
  } else if (c=='+' || c=='-') {
    if (!parseInteger(command,value)||value<-4095||value>4095)
      Serial.println(F("Use +10 or -10"));
    else beginManual(wrapTarget((long)target+value));
  } else if ((c=='T'||c=='t') && command[1]=='\0') captureTarget();
  else if (c=='C'||c=='c') {
    if (command[1]<'1'||command[1]>'6'||
        !(command[2]=='\0'||((command[2]=='+'||command[2]=='-')&&command[3]=='\0'))) {
      Serial.println(F("Use C1..C6 (one IDEAL per gear)")); return;
    }
    if (!sensorOK || abs(wrapped(target-raw))>65) {
      Serial.println(F("Too far from target or sensor offline. Use T then C#, or jog."));
      return;
    }
    uint8_t g=(uint8_t)(command[1]-'1');
    ideal[g]=(uint16_t)target;
    selectedGear=alignedGear=g+1;
    stopMotion(); unsavedChanges=true;
    Serial.print(F("RAM IDEAL G"));Serial.print(g+1);
    Serial.print(F("="));Serial.println(ideal[g]);
    Serial.println(F("W saves table to EEPROM when ready."));
  } else if (c=='O'||c=='o') {
    // O<gear><+ or -><number>. E.g. O2+30.
    if (command[1]<'1'||command[1]>'6'||
        (command[2]!='+'&&command[2]!='-')||
        !parseInteger(command+3,value)||value<0||value>80) {
      Serial.println(F("Use O2+30 / O2-30; overshift 0..80 counts"));return;
    }
    uint8_t g=(uint8_t)(command[1]-'1');
    uint8_t d=command[2]=='+'?FROM_LOWER:FROM_HIGHER;
    overshift[g][d]=(uint8_t)value;
    unsavedChanges=true;
    Serial.print(F("RAM O"));Serial.print(g+1);
    Serial.print(command[2]);Serial.print(F("="));Serial.println(overshift[g][d]);
  } else if (c=='F'||c=='f'||c=='H'||c=='h') {
    if (!parseInteger(command+1,value)||value<0||value>255||
        ((c=='F'||c=='f')&&value<100)||
        ((c=='H'||c=='h')&&value<80)) {
      Serial.println(F("Use F100..255 or H80..255"));return;
    }
    if (c=='F'||c=='f') fastPwm=value;
    else returnPwm=value;
    unsavedChanges=true;
    Serial.println(F("Shift PWM updated (W to save)."));
  } else if (c=='L'||c=='l') printTable();
  else if (c=='W'||c=='w') saveConfig();
  else if (c=='E'||c=='e') {
    stopMotion();setDefaultTable();
    if (!loadConfig()) Serial.println(F("No valid EEPROM config; RAM defaults."));
    inferGear();printTable();
  } else if (c=='G'||c=='g') {
    if (parseInteger(command+1,value)&&value>=1&&value<=GEAR_COUNT) {
      stopMotion();
      selectedGear=(uint8_t)value;
      alignedGear=(ideal[selectedGear-1]!=UNSET &&
        abs(wrapped((int)ideal[selectedGear-1]-raw))<=FINAL_TOL) ? selectedGear : 0;
      Serial.print(F("SELECTED GEAR="));Serial.println(selectedGear);
    } else Serial.println(F("Use G1..G6 to declare selected gear."));
  } else if (c=='>') shiftGear(+1);
  else if (c=='<') shiftGear(-1);
  else if (c=='s'||c=='S') {
    stopMotion();alignedGear=0;
    Serial.println(F("STOPPED: no fault latch; buttons remain enabled."));
  } else if (c=='r'||c=='R') {
    stopMotion(); reversePolarity=!reversePolarity;
    unsavedChanges=true;
    Serial.println(reversePolarity?F("POLARITY REV"):F("POLARITY NORM"));
  } else if (c=='p'||c=='P') showStatus();
  else if (c=='?') help();
  else if (c=='Z'||c=='z') {
    if (command[1]=='0'&&command[2]=='\0') {
      autoSleep=false;bootSerialEntryEnabled=false;
      serialWakePending=false;serialConfirmChars=0;
      Serial.println(F("AUTO_SLEEP OFF"));
    } else if (command[1]=='1'&&command[2]=='\0') {
      // The user explicitly exits calibration; save any changes first.
      if (phase!=IDLE) {
        Serial.println(F("Stop or finish movement before Z1 (s = stop)."));
        return;
      }
      if (unsavedChanges) {
        saveConfig();
        if (unsavedChanges) {
          Serial.println(F("EEPROM verification failed; calibration still active."));
          return;
        }
      }
      autoSleep=true;
      bootSerialEntryEnabled=false; // no auto-reentry from UART bytes
      serialWakePending=false;serialConfirmChars=0;
      forceSleepRequested=false;
      lastActivity=millis();
      Serial.println(F("CALIBRATION FINISHED: auto sleep enabled."));
    } else if (command[1]=='\0') {
      // Honor Z immediately, even in Z0 calibration mode, when idle.
      if (phase==IDLE && digitalRead(BUTTON_PLUS)==HIGH && digitalRead(BUTTON_MINUS)==HIGH) {
        forceSleepRequested=true;
        Serial.println(F("SLEEP requested (button will wake)."));
      } else Serial.println(F("Busy or button held; not sleeping now."));
    } else Serial.println(F("Use Z0, Z1 or Z"));
  } else if (c=='d'||c=='D'||c=='k'||c=='K'||c=='b'||c=='B'||
             c=='u'||c=='U'||c=='v'||c=='V') {
    if (!parseInteger(command+1,value)) {
      Serial.println(F("Use numeric parameter, e.g. u180"));return;
    }
    if (c=='d'||c=='D') deadband=constrain(value,1L,500L);
    if (c=='k'||c=='K') kp100=constrain(value,1L,150L);
    if (c=='b'||c=='B') kd=constrain(value,0L,30L);
    if (c=='u'||c=='U') pwmMin=constrain(value,0L,250L);
    if (c=='v'||c=='V') pwmMax=constrain(value,1L,255L);
    if (pwmMin>pwmMax) pwmMin=pwmMax;
    unsavedChanges=true;
    Serial.println(F("Manual PD parameter updated. W to save."));
  } else Serial.println(F("Unknown command; ? shows help."));
  lastActivity=millis();
}
void enterCalibrationFromSerial() {
  autoSleep=false;
  bootSerialEntryEnabled=false;
  serialWakePending=false;
  serialConfirmChars=0;
  forceSleepRequested=false;
  commandLength=0;lastByte=0;
  // The UART cannot receive the first wake byte reliably when powered down.
  // Do not interpret it: a partial numeric command could move the motor.
  delay(WAKE_RX_DRAIN_MS);
  while (Serial.available()) (void)Serial.read();
  lastActivity=millis();
  Serial.println(F("CALIBRATION MODE. Awake until Z1."));
  Serial.println(F("First serial transmission discarded; enter commands now."));
  Serial.println(F("Z1 saves unsaved calibration and enables auto sleep."));
}
void readSerial() {
  if (autoSleep) {
    // IMPORTANT: a PB3 edge is NOT permission to disable sleep forever.
    // Stay awake for at most 6s waiting for TWO MATCHING printable bytes.
    // The first burst wakes the MCU; after it prints WAKE=PB3, send "xx".
    if (millis()>=bootGraceEnd) bootSerialEntryEnabled=false;
    if (serialWakePending &&
        (long)(millis()-serialConfirmDeadline)>=0) {
      serialWakePending=false;
      serialConfirmChars=0;
      serialConfirmTimeouts++;
      lastActivity=millis()-SLEEP_IDLE_MS; // retry Power-Down immediately
      Serial.println(F("PB3 wake unconfirmed: returning to auto sleep."));
    }
    bool accepting=serialWakePending ||
                   (bootSerialEntryEnabled && millis()<bootGraceEnd);
    while (Serial.available()) {
      char c=(char)Serial.read();
      if (accepting && c>=33 && c<=126) {
        if (serialConfirmChars && c==serialConfirmFirst) {
          ++serialConfirmChars;
        } else {
          serialConfirmFirst=c;
          serialConfirmChars=1;
        }
        if (serialConfirmChars>=SERIAL_CONFIRM_CHARS) {
          enterCalibrationFromSerial();
          return; // never interpret wake bytes as motor/calibration commands
        }
      }
    }
    commandLength=0;
    return;
  }
  while (Serial.available()) {
    char c=(char)Serial.read();
    lastActivity=millis();
    if (c=='\r'||c=='\n'||c==' '||c=='\t') runCommand();
    else if (c>=32&&c<=126&&commandLength<sizeof(command)-1) {
      command[commandLength++]=c;
      lastByte=millis();
    }
  }
  if (commandLength && millis()-lastByte>120) runCommand();
}
void initButton(DebouncedButton &button, uint8_t pin) {
  button.pin=pin;
  pinMode(pin,INPUT_PULLUP);
  button.lastReading=button.stable=digitalRead(pin);
  button.changedAt=millis();
}
bool pressEvent(DebouncedButton &button, unsigned long now) {
  bool reading=digitalRead(button.pin);
  if (reading!=button.lastReading) {
    button.lastReading=reading; button.changedAt=now;
  }
  if (now-button.changedAt>=DEBOUNCE_MS && reading!=button.stable) {
    button.stable=reading;
    return reading==LOW;
  }
  return false;
}
void readButtons(unsigned long now) {
  // Read and clear ISR-latched press edges atomically.  The MCU may have
  // missed a short tap with the old 35 ms continuous-level polling logic.
  uint8_t edges;
  uint8_t savedSREG=SREG;
  cli();
  edges=buttonEdges;
  buttonEdges=0;
  // V6 FIX: wakeButtons also accumulates while fully awake.  If not cleared
  // here, the last DOWN press on gear 1 remains latched through sleep and
  // combines with a new UP wake press (mask 3), which gets ignored.  Same
  // problem occurs at gear 6 when reversing from UP to DOWN.  Clear BOTH
  // latches in the same atomic transaction; fresh sleep button interrupts
  // will then capture only the actual new wake press.
  wakeButtons=0;
  SREG=savedSREG;

  updateRearm(plusArmed,plusHighSince,BUTTON_PLUS,now);
  updateRearm(minusArmed,minusHighSince,BUTTON_MINUS,now);
  if (!edges) return;
  // A physical button has precedence over any unconfirmed serial wake.
  serialWakePending=false;
  serialConfirmChars=0;
  lastActivity=now;

  // Simultaneous buttons are deliberately ignored, as before.
  if ((edges&3)==3 ||
      (digitalRead(BUTTON_PLUS)==LOW && digitalRead(BUTTON_MINUS)==LOW)) {
    if (edges&1) {plusArmed=false;plusHighSince=0;}
    if (edges&2) {minusArmed=false;minusHighSince=0;}
    return;
  }
  if ((edges&1) && plusArmed) {
    plusArmed=false;plusHighSince=0;
    acceptedPlus++;
    shiftGear(+1);
  }
  if ((edges&2) && minusArmed) {
    minusArmed=false;minusHighSince=0;
    acceptedMinus++;
    shiftGear(-1);
  }
}

// Original motor PD loop is retained for manual position changes only.
// Normal gear shifts use stronger, decisive PWM with temporary overshift.
void controlStep() {
  int a;
  if (!readAngle(a)) {
    if (sensorOK) Serial.println(F("AS5600 READ FAILED; motor off (NO latch)"));
    sensorOK=false; stopMotion(); alignedGear=0;
    return;
  }
  if (!sensorOK) {
    sensorOK=true;
    raw=oldRaw=a;velocityQ8=0;
    return;
  }
  raw=a;
  int delta=wrapped(raw-oldRaw);
  oldRaw=raw;
  if (abs(delta)>=2) lastEncoderChange=millis();
  velocityQ8+=(((long)delta*256)-velocityQ8)/4;
  if (phase==IDLE) return;
  unsigned long now=millis();
  if (abs(wrapped(raw-movementRaw))>=3) {
    movementRaw=raw;
    lastMovement=now;
  }
  if (phase==OVERSHIFT_HOLD) {
    if (now-phaseStart>=COMPLETE_HOLD_MS) {
      target=finalIdeal;
      phase=RETURN_IDEAL;
      resetLeg(now);
    }
    return;
  }

  int e=controlError();
  int tol=(phase==TO_OVERSHIFT)?OVERSHIFT_TOL:FINAL_TOL;
  bool arrived=abs(e)<=tol;
  if (legDirection!=0 && ((legDirection>0&&e<0)||(legDirection<0&&e>0))) {
    // We crossed the goal: don't reverse full PWM and hunt.
    arrived=true;
  }
  if (arrived) {
    motorBrake();
    if (phase==TO_OVERSHIFT && target!=finalIdeal) {
      phase=OVERSHIFT_HOLD;
      phaseStart=now;
      return;
    }
    if (phase==TO_OVERSHIFT || phase==RETURN_IDEAL) {
      if (abs(wrapped(finalIdeal-raw))<=deadband+5) {
        alignedGear=movingToGear;
        Serial.print(F("ENCODER AT GEAR "));Serial.println(alignedGear);
      } else {
        alignedGear=0;
        Serial.println(F("Stopped beyond ideal tolerance; encoder not aligned."));
      }
    }
    stopMotion();
    lastActivity=now;
    return;
  }

  if (now-phaseStart>STAGE_TIMEOUT_MS) {
    terminateMove(F("motion stage timeout"));return;
  }
  // Only run no-motion protection when drive actually applied.
  if (appliedPWM>0 && now-lastMovement>NO_MOTION_TIMEOUT_MS) {
    terminateMove(F("no encoder movement"));return;
  }
  if (phase==MANUAL_MOVE) {
    long effort=((long)e*kp100)/100-(velocityQ8*kd)/256;
    if (abs(effort)<12 || (e>0&&effort<=0)||(e<0&&effort>=0)) {
      motorBrake();
      // No endless brake/pause loop: stop if controller ceases driving.
      stopMotion();lastActivity=now;
      return;
    }
    int pwm=(int)constrain(abs(effort),(long)pwmMin,(long)pwmMax);
    motorDrive(e>0?1:-1,pwm);
    if (!legDirection) legDirection=e>0?1:-1;
    return;
  }
  if (!legDirection) legDirection=e>0?1:-1;
  // Drive in the original direction; brake if target crossed (above).
  motorDrive(legDirection, phase==TO_OVERSHIFT ? fastPwm:returnPwm);
}

void disableUnusedInputs() {
  PORTA.PIN1CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTA.PIN7CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTB.PIN4CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTB.PIN5CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTC.PIN0CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTC.PIN1CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTC.PIN3CTRL=PORT_ISC_INPUT_DISABLE_gc;
}

void enterDeepSleep() {
  if (buttonEdges || serialWakePending) return;
  // V3: never lose a captured short button tap
  motorOff();
  sensorPowerDown();
  Serial.flush();
  Serial.end();

  // Keep V3 button interrupts continuously armed, including Power-Down.
  uint8_t pb0=PORTB.PIN0CTRL,pb1=PORTB.PIN1CTRL;
  uint8_t pb2=PORTB.PIN2CTRL,pb3=PORTB.PIN3CTRL;
  uint8_t savedADC=ADC0.CTRLA;
  pinMode(PIN_PB2,INPUT);
  pinMode(PIN_PB3,INPUT_PULLUP);
  ADC0.CTRLA &= (uint8_t)~ADC_ENABLE_bm;
  PORTB.PIN0CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTB.PIN1CTRL=PORT_ISC_INPUT_DISABLE_gc;
  PORTB.PIN2CTRL=PORT_ISC_INPUT_DISABLE_gc;

  // An unplugged or actively LOW FTDI RX line must not prevent low-current
  // sleep. If low, disable that interrupt for this sleep cycle and keep
  // button wake working. PB3 serial wake requires the line to idle HIGH.
  const bool serialWakeArmed=(digitalRead(PIN_PB3)==HIGH);
  wakeSerial=false;
  if (serialWakeArmed) {
    attachInterrupt(digitalPinToInterrupt(PIN_PB3),wakeSerialISR,CHANGE);
    PORTB.INTFLAGS=PIN3_bm; // clear any stale pin-change flag on arming
  } else {
    PORTB.PIN3CTRL=PORT_ISC_INPUT_DISABLE_gc;
  }

  set_sleep_mode(SLEEP_MODE_PWR_DOWN);
  bool actuallySlept=false;
  cli();
  const bool buttonsIdle=(digitalRead(BUTTON_PLUS)==HIGH &&
                          digitalRead(BUTTON_MINUS)==HIGH);
  if (buttonsIdle && buttonEdges==0) {
    sleep_enable();
    actuallySlept=true;
    sei();
    sleep_cpu();
    sleep_disable();
  } else {
    sei();
  }

  // V3: collect an interrupt-latched short press even if already released.
  uint8_t woke;
  uint8_t savedSREG=SREG;
  cli();
  woke=wakeButtons | buttonEdges;
  buttonEdges=0;
  wakeButtons=0;
  SREG=savedSREG;
  if (digitalRead(BUTTON_PLUS)==LOW) woke|=1;
  if (digitalRead(BUTTON_MINUS)==LOW) woke|=2;

  // IMPORTANT: a skipped/aborted attempt is NOT a serial wake.
  // PB3 is partially asynchronous: a short pulse can wake the core
  // without setting an ISR flag (Microchip datasheet 17.3.3.1). Treat an
  // unexplained wake as a CANDIDATE only, never as calibration itself.
  // Two identical printable UART characters must subsequently confirm it.
  const bool possibleSerialWake=(actuallySlept && serialWakeArmed && woke==0);
  if (serialWakeArmed) detachInterrupt(digitalPinToInterrupt(PIN_PB3));
  PORTB.PIN0CTRL=pb0;PORTB.PIN1CTRL=pb1;
  PORTB.PIN2CTRL=pb2;PORTB.PIN3CTRL=pb3;
  ADC0.CTRLA=savedADC;

  Serial.begin(115200);
  sensorPowerUp();
  int a;
  sensorOK=readAngle(a);
  if (sensorOK) {
    raw=oldRaw=target=a;
    velocityQ8=0;halfTurnLock=false;
    if (!selectedGear) inferGear();
  }
  initButton(plusButton,BUTTON_PLUS);
  initButton(minusButton,BUTTON_MINUS);
  phase=IDLE;movingToGear=0;
  lastActivity=lastEncoderChange=millis();
  lastControl=lastReport=millis();

  // Never reopen the boot-only UART entry window on a button wake.
  bootSerialEntryEnabled=false;
  serialWakePending=false;
  serialConfirmChars=0;
  if (possibleSerialWake) {
    if (wakeSerial) serialWakes++; else unknownWakes++;
    // Do NOT disable autoSleep until UART characters confirm user intent.
    serialWakePending=true;
    serialConfirmDeadline=millis()+SERIAL_CONFIRM_MS;
    Serial.println(F("WAKE=PB3/OTHER: send xx within 6 seconds to calibrate."));
  } else if (actuallySlept) {
    if (woke) {
      buttonWakes++;
      Serial.print(F("WAKE=BUTTON MASK="));Serial.println(woke);
    } else {
      unknownWakes++;
      Serial.println(F("WAKE=OTHER (not entering calibration)"));
    }
    if (woke&1) {plusArmed=false;plusHighSince=0;}
    if (woke&2) {minusArmed=false;minusHighSince=0;}
    if (!sensorOK) {
      Serial.println(F("AS5600 unavailable; no motor drive."));
    } else if (woke==1||woke==2) {
      if (woke==1) acceptedPlus++; else acceptedMinus++;
      shiftGear(woke==1?+1:-1);
    }
  }
  initButton(plusButton,BUTTON_PLUS);
  initButton(minusButton,BUTTON_MINUS);
}

void setup() {
  disableUnusedInputs();
  pinMode(IN1,OUTPUT);pinMode(IN2,OUTPUT);pinMode(NSLEEP,OUTPUT);
  motorOff();
  pinMode(SENSOR_POWER,OUTPUT);digitalWrite(SENSOR_POWER,LOW);
  Serial.begin(115200);
  sensorPowerUp();
  initButton(plusButton,BUTTON_PLUS);
  initButton(minusButton,BUTTON_MINUS);
  // PC2 and PA2 support fully asynchronous wake; capture CHANGE-to-LOW
  // while running and sleeping alike.
  attachInterrupt(digitalPinToInterrupt(BUTTON_PLUS),wakePlusISR,CHANGE);
  attachInterrupt(digitalPinToInterrupt(BUTTON_MINUS),wakeMinusISR,CHANGE);
  setDefaultTable();
  delay(200);
  loadConfig();
  sensorOK=readAngle(raw);
  if (sensorOK) {
    target=oldRaw=raw;
    inferGear();
  }
  Serial.println(F("ATtiny3226 / BUTTON CAPTURE V3 + SERIAL CONFIRM V6"));
  Serial.println(F("No startup motor motion. PC2 +, PA2 -."));
  help();printTable();showStatus();
  lastControl=lastReport=millis();
  lastActivity=lastEncoderChange=millis();
  bootGraceEnd=millis()+BOOT_SERIAL_GRACE_MS;
}
void loop() {
  readSerial();
  unsigned long now=millis();
  readButtons(now);
  if (now-lastControl>=10) {
    lastControl=now;
    controlStep();
  }
  if (now-lastReport>=1000) {
    lastReport=now;
    showStatus();
  }
  // Never block shifting due to a latched fault: there is NO fault latch.
  // Any stopped or timed-out motion can sleep, then respond to next button.
  bool sleepNow=(forceSleepRequested ||
      (autoSleep && !serialWakePending && now>=bootGraceEnd &&
       now-lastActivity>=SLEEP_IDLE_MS));
  // Z1 saves changed calibration before re-enabling auto sleep.
  // W also saves explicitly; unsaved RAM settings never survive battery loss.
  // Encoder jitter is not a reason to stay awake forever after motor IDLE.
  // lastActivity already provides the necessary settle time for every shift.
  if (sleepNow && phase==IDLE && commandLength==0 &&
      digitalRead(BUTTON_PLUS)==HIGH && digitalRead(BUTTON_MINUS)==HIGH) {
    forceSleepRequested=false;
    enterDeepSleep();
  }
}
