# SCXML on an ATMega328 {#embedded}

<!-- https://sourceforge.net/p/doxygen/discussion/markdown_syntax -->

[TOC]

This page describes how to use SCXML to model the control flow for an embedded micro-controller. We will transform an SCXML state-chart onto ANSI-C, provide some scaffolding and deploy it onto the Arduino Nano. Regardless of the target platform, the approach is the same if you like to use the ANSI-C transformation for just any other platform.

\section platform Hardware Platform

For a project of mine, I used a solar-powered Arduino Nano to control four aquarium pumps to water my balcony plants when their soil is dry. There are some peculiarities that justify to use a state-chart to model the controller's behavior, namely:

1. There is only enough power for one pump at a time
2. Pumps should only run if there is sufficient sunlight
3. The pump related to the sensor with the driest soil below a given threshold should run
4. If a pump runs, it ought to run for a given minimum amount of time

The whole system is powered via a 5W solar module, which is connected via a 12V DCDC converter to another 12V5V DCDC converter, allowing to operate the actuators with 12V and the Arduino with 5V. On the 12V potential, there are some gold caps worth ~150mF to stabilize the potential and provide some *kick-off* current for a pump to start.

\subsection sensors Sensors

In order to measure the soil's moisture, I originally bought those cheap moisture sensors that will measure conductivity between two zinc plated conductors. The problem with these is that they corrode pretty quickly. You can alleviate the problem somewhat by measuring only once every N minutes, but still I disliked the approach.

That's why I went for capacitive sensors with some nice aluminum plates that I can either drop into the water reservoir of my balcony's flower beds or bury at the edge of a bed. Moist soil will cause a higher capacity and we can measure it very easily with two digital pins on the ATMega328: Just set the first pin to `HIGH` and measure the time it takes for a second pin, connected to the same potential to read `HIGH`. The longer it took to achieve the `HIGH` potential on the second pin, the higher the capacity, the more moist the soil.

There is another sensor as a simple voltage divider with 1M Ohm and 100K Ohm to measure the voltage at the solar module. This will allow us only to water plants when the sun is actually shining and with sufficient strength.

\subsection actuators Actuators

I connected four 3W aquarium pumps via relais that I supply with 12V from the solar module and control via analog outputs from the Arduino as most digital outputs are taken by the capacitive sensors for the soil's moisture. The pumps are submerged in a 60l tank of water that I have to refill occasionally.

\section control_logic Control Logic

Initially, I developed the system as a pet project but soon realized that I could utilize a state-chart to, more formally, adhere to the requirements above. Here is the SCXML document I wrote:

\includelineno apps/arduino/WaterPump.scxml

There are a few noteworthy things in the SCXML document above:

* Datamodel attribute is `native and no datamodel element is given
    * This will cause the transpilation process to include all datamodel statements and expressions *as is* in the generated source, without passing them to a user-supplied callback for interpretation.
    * Using this approach, it is no longer possible to interpret the document with the browser.
* We can use identifiers and functions available on the Arduino platform
    * As all expressions and statements will be inserted verbatim into the generated ANSI-C file, and will merely compile it as any other file when we deploy on the Arduino.
* Content of script elements is in CDATA sections while expressions in conditions are escaped
    * We are using the [DOMLSSerializer](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/util/DOM.cpp#L36) to create a textual representation of the XML DOM and I could not convince it to unescape XML entities when writing the stream.
* We assume a `pump` and a `capsense` invoker
    * Indeed, we will not write proper invokers but just mock them in the scaffolding. The important thing is that we get the lifetime management from the SCXML semantics.

When we transform this document via `uscxml-transform -tc -i WaterPump.scxml -o stateMachine.c` we will arrive at a [stateMachine.c file](https://github.com/tklab-tud/uscxml/tree/master/apps/arduino/stateMachine.c) which conforms to the control flow modeled in the SCXML file. Now, we will need to write the scaffolding that connects the callbacks and starts the machine. The complete scaffolding for the generated state machine is given below:

\includelineno apps/arduino/WaterPump.cxx

To integrate the scaffolding and the control logic from the state-chart, the generated `stateMachine.c` is merely included into the compilation unit. To compile it all, I am using [PlatformIO](http://platformio.org) IDE as it is more convenient to work with multifile projects as apposed to the [Arduino IDE](https://www.arduino.cc/en/Main/Software), but both will work. It is important, not to compile `stateMachine.c` as a distinct compilation unit, but only as part of the scaffolding. If you have any problems to exclude it from the build process, you may always rename it into something without a `.c` extension.

The scaffolding is rather minimal and somewhat unorthodox as I tried to get away without using `malloc` for dynamic memory allocations, but keep everything on the stack. Let's walk through the individual lines:

* First we include the header files for [LowPower](https://github.com/rocketscream/Low-Power) and [CapacitiveSensor](https://github.com/PaulStoffregen/CapacitiveSensor). With PlatformIO, you will have to copy them into your `lib` directory along with their respective implementations.
* Then we declare some macros that define constant values. Noteworthy is the `USCXML_NO_HISTORY` macro which causes the generated ANSI-C to drop a block of code for processing history elements, which we do not use.
* Afterwards, we declare and define variables. We could have them as part of a `datamodel` element in the original SCXML document, but in my opinion, defining them here makes their existence more explicit.
* It is noteworthy that we do enumerate all the events we are going to pass and will not implement an actual queue of events. A proper queue would require malloc and there will never be more than one event to consider per microstep.
* In line 62, we include the generated ANSI-C stateMachine and define a context, as it is required to represent the state of a state-chart.
* Then we define the callbacks that we later connect to the state-chart's context:
    * `invoke` will be called whenever an invocation is to be started or stopped at the end of a macro-step. This is where we merely remember whether we are supposed to start a pump (type `pump`) or deliver sensor readings from the capacitive sensors (type `capsense`).
    * `matched` is called to determine whether a given transition's event descriptor is matched by a given event and a concept explained in more detail in the SCXML recommendation. In this implementation, we ignore the finer points of event descriptor matching and only match, when the event's name is a literal match for the transition's event. attribute
    * `send`: When we start a pump, we are sending a delayed event to ourselves which we will have to deliver back into the state-chart after the given time in milliseconds passed. We just remember the current delay in `pumpRemain` and, subsequently, decrease it until we reach the timeout and have to deliver it.
    * `dequeueExternal`: Whenever the interpreter is in a stable configuration, it makes an attempt to dequeue an external event, which will cause this callback to be triggered. If we return an event, it will be processed by triggering transitions and a change in the configuration, if we return `NULL`, the state-chart will `IDLE`.
    * `isInState` is not formally a callback to be registered by the context but very useful to dispatch upon the configuration of the state chart later.
* In `setup`, we initialize the state of the platform after the `reset` button is pressed or the power came back on. I.e. we connect the callbacks and initialize the state chart by proceeding to the first `IDLE` interpreter state.
* In `loop` we process one cycle of the controller. We turn the LED on to indicate that we are processing and read the capacitive sensors if the invoker is active. Then we read the amount of light that arrives at the solar module via the voltage divider connected to `LIGHT` and transition accordingly. Afterwards we check if it is time to send the eventual `idle` event to turn of the pumps or check if we ought to activate a pump.

One thing that helped me when developing the scaffolding was to thing about the configuration the state chart would eventually be in and observe the various events it would react to. Then to make sure that these events would be delivered when they are relevant.

\section resources Resources

The resources required when deploying this program on the ATMega328 are given as follows:

    Program:   10534 bytes (32.1% Full)
    (.text + .data + .bootloader)
    
    Data:       1636 bytes (79.9% Full)
    (.data + .bss + .noinit)

There are still quite some possibilities to reduce these resources some more if we are pressed on space:

* Event and invoker names can be enumerated
* We can drop some unused callbacks from the `uscxm_ctx` struct
* We can remove most fields of the `uscxml_elem_send` struct
