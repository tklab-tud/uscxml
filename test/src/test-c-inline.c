//#include <stdlib.h> // EXIT_SUCCESS
//#include <stdio.h> // printf
#include <string.h> // memset

#undef ON_AVR

/**
 * Preprocess:
 * uscxml-transform -tc -i ./gadget-inline-avr.c -o ./gadget-inline-avr.c.scxml.c
 */

/** INLINE SCXML BEGIN

<scxml>
  <parallel>
    <onentry>
        <raise event="blueHigh" />
    </onentry>
    <!-- 
      1 X X X X
      ^ ^^^ ^^^
      |  |   |
      |  |   Action
      |  Color
      Here comes the signal!
      
      Colors:
      blue   1,1
      red    1,0
      green  0,1
      ESC!   0,0
      
      Actions:
      dimUp:    0,1
      dimDown:  0,0
      turnOn:   1,1
      turnDown: 1,0
      
      ESC!:
      0,0  All off
      1,1  All on
      
      IR emitter is either Color + Action or Special
    -->
    <state id="interaction">
      <transition event="blueHigh">
        <!-- Receiver beware, here it comes -->
        <raise event="IROn" />

        <!-- color blue -->
        <raise event="IROn" />
        <raise event="IROn" />
        
        <!-- action dimUp -->
        <raise event="IROff" />
        <raise event="IROn" />

        <!-- make sure to turn LED off -->
        <raise event="IROff" />

      </transition>
    </state>
    
    <state id="periphery">
      <transition event="IROn" target="IRLedOn" type="internal" />
      <transition event="IROff" target="IRLedOff" type="internal" />

      <!-- These are the lines we will connect to the IR emitter -->
      <state id="IRLedOff">
        <onentry>ledOff();</onentry>
      </state>
      <state id="IRLedOn">
        <onentry>ledOn();</onentry>
      </state>
    </state>
  </parallel>
</scxml>
INLINE SCXML END */ 

#define IQ_LENGTH 10
#define EQ_LENGTH 10

const char* iQ[IQ_LENGTH];
size_t iwPtr = 0;
size_t irPtr = 0;

const char* eQ[EQ_LENGTH];
size_t ewPtr = 0;
size_t erPtr = 0;


void ledOn() {
	printf("Turned on LED!\n");
}

void ledOff() {
    printf("Turned off LED!\n");
}

#include "test-c-inline.c.scxml.c"

void* dequeue_internal(const uscxml_ctx* ctx) {
    if (iwPtr != irPtr) {
        size_t tmp = irPtr;
        irPtr = (irPtr + 1 >= IQ_LENGTH ? 0 : irPtr + 1);
        return iQ[tmp];
    }
    return NULL;
}

void* dequeue_external(const uscxml_ctx* ctx) {
    if (ewPtr != erPtr) {
        size_t tmp = erPtr;
        irPtr = (erPtr + 1 >= EQ_LENGTH ? 0 : erPtr + 1);
        return eQ[tmp];
    }
    return NULL;
}

int is_matched(const uscxml_ctx* ctx, const uscxml_transition* transition, const void* event) {
    char* tPtr1 = (char*)event;
    char* tPtr2 = (char*)transition->event;
    while(*tPtr1 && *tPtr2) {
        if (tPtr1 != tPtr2)
            return 0;
        tPtr1++;
        tPtr2++;
    }
    return 1;
}

int raise(const uscxml_ctx* ctx, const char* event) {
    iQ[iwPtr] = event;
    iwPtr = (iwPtr + 1 >= IQ_LENGTH ? 0 : iwPtr + 1);
    return USCXML_ERR_OK;
}

int send(const uscxml_ctx* ctx, const char* event) {
    eQ[ewPtr] = event;
    ewPtr = (ewPtr + 1 >= IQ_LENGTH ? 0 : ewPtr + 1);
    return USCXML_ERR_OK;
}

int main(int argc, char** argv) {

#ifdef ON_AVR
    int ir_led = 9;
    int blue_touch = 1;
    int red_touch = 2;
    int yellow_touch = 3;
    
    pinMode(ir_led, OUTPUT);
    pinMode(blue_touch, INPUT);
    pinMode(red_touch, INPUT);
    pinMode(yellow_touch, INPUT);

#endif
    
    
	uscxml_ctx ctx;
	int err = USCXML_ERR_OK;

	memset(&ctx, 0, sizeof(uscxml_ctx));
	ctx.machine = &USCXML_MACHINE;
    
    ctx.exec_content_raise = raise;
    ctx.dequeue_internal = dequeue_internal;
    ctx.dequeue_external = dequeue_external;
    ctx.is_matched = is_matched;
    
	while(err != USCXML_ERR_DONE) {
        
		err = uscxml_step(&ctx);
#ifdef ON_AVR
        if (err == USCXML_IDLE) {
            if (digitalRead(blue) == HIGH) {
                send(ctx, "blueHigh");
            }
            if (digitalRead(blue) == HIGH) {
                send(ctx, "redHigh");
            }
            if (digitalRead(blue) == HIGH) {
                send(ctx, "greenHigh");
            }
        }
        delay(20);
#endif
	}
	
	return 0;
}
