// Resources:
// https://www.avrprogrammers.com/howto/atmega328-power
// https://github.com/PaulStoffregen/CapacitiveSensor
// https://de.wikipedia.org/wiki/Faustformelverfahren_%28Automatisierungstechnik%29
// http://brettbeauregard.com/blog/2011/04/improving-the-beginners-pid-introduction/
// google://SCC3 for conformal coating

#include <LowPower.h> 
#include <CapacitiveSensor.h> 


#define USCXML_NO_HISTORY

#define LED 13                     // LED pin on the Arduino Nano
#define LIGHT A7                   // 1:10 voltage divider soldered into the solar panel
#define LIGHT_THRES 300            // do not actuate beneath this brightness
#define MEASURE_INTERVAL SLEEP_1S  // time between cycles
#define DARK_SLEEP_CYCLES 1

#define PUMP_ON LOW                // Setting an output to LOW will trigger the relais
#define PUMP_OFF HIGH

#define ROLLOFF 0.8                // exponential smoothing for sensor readings

float soil[4] = { 0, 0, 0, 0 };    // smoothed sensor readings from the capacitive sensors
int pump[4] = { A0, A1, A2, A3 };  // we abuse analog pins as digital output
int activePump = -1;

int thrs[4] = { 1400, 1400, 1400, 1400 }; // start pumping below these values

CapacitiveSensor bed[4] = {        // Pins where the capacitive sensors are connected
  CapacitiveSensor(3, 2),
  CapacitiveSensor(5, 4),
  CapacitiveSensor(7, 6),
  CapacitiveSensor(9, 8)
};
char readCapSense = 0;             // Whether the capsense invoker is active

struct data_t {
  int light;
};
struct event_t {
  const char* name;
  struct data_t data;
};

// the various events
long pumpRemain = 0;
struct event_t _eventIdle = {
  name: "idle"
};
struct event_t _eventLight = {
  name: "light"
};
struct event_t _eventPump = {
  name: "pump"
};
struct event_t* _event;

#include "stateMachine.c"

uscxml_ctx ctx;

/* state chart is invoking something */
static int invoke(const uscxml_ctx* ctx,
                  const uscxml_state* s,
                  const uscxml_elem_invoke* invocation,
                  unsigned char uninvoke) {
  if (strcmp(invocation->type, "pump") == 0) {
    int pumpId = atoi(invocation->id);
    digitalWrite(pump[pumpId], uninvoke == 0 ? PUMP_ON : PUMP_OFF);
  } else if (strcmp(invocation->type, "capsense") == 0) {
    readCapSense = uninvoke;
  }
}

/* is the event matching */
static int matched(const uscxml_ctx* ctx,
                   const uscxml_transition* transition,
                   const void* event) {
  // we ignore most event name matching rules here
  return strcmp(transition->event, ((const struct event_t*)event)->name) == 0;
}

static int send(const uscxml_ctx* ctx, const uscxml_elem_send* send) {
  if (send->delay > 0)
    pumpRemain = send->delay;
  return USCXML_ERR_OK;
}

static void* dequeueExternal(const uscxml_ctx* ctx) {
  // we will only call step when we have an event
  void* tmp = _event;
  _event = NULL;
  return tmp;
}

static bool isInState(const char* stateId) {
  for (size_t i = 0; i < ctx.machine->nr_states; i++) {
    if (ctx.machine->states[i].name &&
            strcmp(ctx.machine->states[i].name, stateId) == 0 &&
            BIT_HAS(i, ctx.config)) {
      return true;
    }
  }

  return false;
}

void setup() {
  // initilize the state chart
  memset(&ctx, 0, sizeof(uscxml_ctx));
  ctx.machine = &USCXML_MACHINE;
  ctx.invoke = invoke;
  ctx.is_matched = matched;
  ctx.dequeue_external = dequeueExternal;
  ctx.exec_content_send = send;

  int err = USCXML_ERR_OK;

  // run until first stable config
  while((err = uscxml_step(&ctx)) != USCXML_ERR_IDLE) {}
}


void loop() {
  digitalWrite(LED, HIGH);

  int err = USCXML_ERR_OK;

  if (readCapSense) {
    // capsense invoker is active
    for (int i = 0; i < 4; ++i) {
      int cap = bed[i].capacitiveSensor(50);
      if (cap > 0) {
        soil[i] = ROLLOFF * soil[i] + (1 - ROLLOFF) * (cap - thrs[i]);
      }
    }
  }

  _eventLight.data.light = analogRead(LIGHT);
  _event = &_eventLight;
  while((err = uscxml_step(&ctx)) != USCXML_ERR_IDLE) {}

  if (isInState("dark")) {
    LowPower.powerDown(MEASURE_INTERVAL, ADC_OFF, BOD_OFF);
    return;
  }

  if (isInState("light")) {
    if (false) {
    } else if (isInState("pumping")) {
      // is time elapsed already?
      if (pumpRemain == 0) {
        _event = &_eventIdle;
        while((err = uscxml_step(&ctx)) != USCXML_ERR_IDLE) {}
      }
    } else if (isInState("idle")) {
      // check is we need to pump
      _event = &_eventPump;
      while((err = uscxml_step(&ctx)) != USCXML_ERR_IDLE) {}
    }
  }

  pumpRemain = (pumpRemain >= 8000) ? pumpRemain - 8000 : 0;

  digitalWrite(LED, LOW);
  LowPower.powerDown(MEASURE_INTERVAL, ADC_OFF, BOD_OFF);

}
