# Generating Native Code

You can use the <tt>uscxml-transform</tt> tool to create native code from an
SCXML document. In this case, you will not use an instance of the
<tt>uscxml::Interpreter</tt> class, but instantiate an SCXML context from a
native description of the state-chart.

## Embedding ANSI C

To embed the control flow described within an SCXML document in most variances
of the C language, we provide a transformation onto ANSI C (C89) as a proper
subset of virtually any more modern C/C++ dialect. There are two general
approaches to achieve this. In any case, you need to transform your SCXML
state-chart onto ANSI C by invoking <tt>uscxml-transform</tt>:

    $ uscxml-transform -tc -i INPUT_FILE -o OUTPUT_FILE

This transformation will create a single file that you can compile and link or
include directly. I advice to include the file into another compilation unit
and not to compile it directly, as it allows for more convenience and is
generally a more flexible approach. The file will contain:

1. A set of pre-processor **macros** for convenience and definitions, all starting
with an <tt>USCXML_</tt> prefix. Of special note are the following macros that
allow you to influence important characteristics of you state-machine.

    * <tt>**USCXML_NR_STATES_TYPE** / **USCXML_NR_TRANS_TYPE**</tt>: 
    
        The type for unsigned integers that is of sufficient size to contain
        the number of states / transitions of your largest state machine. The
        transformation will automatically choose one of the <tt>uint*_t</tt>
        types, though a popular extension, they are only available in C99
        (<tt>stdint.h</tt>). Also, if you like to reuse parts of the file (e.g.
        the types below) in another compilation unit, you might need to
        predefine them explicitly to a sufficient size.

    * <tt>**USCXML_MAX_NR_STATES_BYTES** / **USCXML_MAX_NR_TRANS_BYTES**</tt>: 

        The minimial size for the bit-arrays as <tt>char[N]</tt> containing the
        states and transitions in the various types and on the stack during a
        microstep. It has to be larger or equal to the smallest positive
        integer that, when multiplied by 8 is larger or equal to the number of
        states and transitions repsectively. 
        
        In other words, make sure that
        <tt>states[USCXML_MAX_NR_STATES_BYTES]</tt> has room for one bit per
        state and <tt>transitions[USCXML_MAX_NR_TRANS_BYTES]</tt> for one bit
        per transition.

    * There are some other macros defined, but they are rather for
      micro-optimizations. Have a look at a generated file.

2. All compound data **types** (<tt>struct</tt>) to encode an SCXML state-machine.
These will refer to the macros above to require memory for a state-chart's
states and transitions, so make sure that the macros are set if you
conditionally include parts of the generated file and double-check that the
type definitions are the same in every compilation unit if you want to access
state-machines from other units (i.e. same value for macros above!).

3. The actual **symbols** for one or many state-machines from the input SCXML
file. Their identifiers are all prefixed by an identifier derived from the
content of a given SCXML document. As such, if you transform any given SCXML
document twice, you might end up with duplicate symbols, yet again, the
state-chart's will be functionally identical as they contained the same content.

    In order for not having to guess the prefix when referring to any machine
    in application code, the tranformation will define three additional macros:

        #ifndef USCXML_MACHINE
        #  define USCXML_MACHINE _uscxml_BC220711_machine
        #endif
        #define USCXML_MACHINE_0 _uscxml_BC220711_machine
        #define USCXML_MACHINE_NAME_HERE _uscxml_BC220711_machine

    The first macro is useful if you only transformed a single SCXML
    state-chart as it will always refer to the very first state-chart
    encountered. If there is more than one SCXML state-chart within a document
    (i.e. an invocation of nested machines) you can also refer to them by index
    or their eventual name.

4. Some **helper functions**, most notably bit operations for arbitrary length
bit arrays.

5. The **micro-step function** <tt>uscxml_step</tt>, which will perform a
micro-step on a given context and delegate control flow accordingly.

These elements are always contained and you can, selectively, disable their
inclusion by pre-defining respective macros (have a look at a generated source
file).

Now in order to actually use an SCXML document to manage the control flow among
a set of functions, there are two general approaches. Both use the generated
ANSI C source code above, but require more or less resources at runtime as
detailled below.

### Fully Compliant

An SCXML interpreter does more than to perform a series of microsteps for event
over a set of states and transitions and there are quite a few responsibilities
not implemented in the generated ANSI C code:

1. **Event Queues**:

    A compliant interpreter is required to maintain two event queues, an
    internal and an external one. With the generated ANSI C source, these are
    integrated via four callbacks and will need to be implemented in
    user-supplied code:
    
    1. <tt>**uscxml_ctx.dequeue_internal**</tt>: This callback is invoked
    whenever the interpreter needs an event from the internal event queue. It
    is passed an instance of a <tt>uscxml_ctx</tt> structure and is supposed to
    return an opaque pointer to an event. If the internal queue is empty,
    <tt>NULL</tt> is to be returned.
    
    2. <tt>**uscxml_ctx.dequeue_external**</tt>: This callback is functionally
    equivalent to <tt>uscxml_ctx.dequeue_internal</tt> but invoked, when an
    external event is to be dequeued.

    3. <tt>**uscxml_ctx.exec_content_send**</tt>: Whenever there is an
    <tt>&lt;send></tt> element encountered in executable content, the generated
    ANSI C code will invoke this callback with a context and an
    <tt>uscxml_elem_send</tt> instance and the user code registered at the
    callback is expected to handle the send request as per recommendation.

    4. <tt>**uscxml_ctx.exec_content_raise**</tt>: This callback is invoked for
    any <tt>&lt;raise></tt> element processed as part of executable content and
    is expected to deliver an event to the internal event queue.
    
2. **Transition Matching / Enabling**

    An event will match and enable a set of transitions. The generated ANSI C
    source will already make sure that only valid sets of transitions can be
    selected to constitute the optimal transition set for a microstep, but
    user-supplied code will have to decide whether a transition is matched and
    enabled. This is done via the <tt>**uscxml_ctx.is_enabled**</tt> callback.
    It receives a context, a <tt>uscxml_transition</tt> structure and the
    opaque event pointer and will have to return <tt>0</tt> for when the
    transition is not matched and enabled by the given event and <tt>1</tt> if
    it is.


### Light-Weight
