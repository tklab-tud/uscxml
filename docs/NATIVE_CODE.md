# Generating Native Code

You can use the <tt>uscxml-transform</tt> tool to create native code from an
SCXML document. In this case, you will not use an instance of the
<tt>uscxml::Interpreter</tt> class, but instantiate an SCXML context from a
native description of the state-chart.

## Embedding ANSI C

To embed the control flow described within an SCXML document in most variances
of the C language, we provide a transformation onto ANSI C (C89) as a proper
subset of virtually any more modern C/C++ dialect. First, you need to transform
your SCXML state-chart onto ANSI C by invoking <tt>uscxml-transform</tt>:

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

    * <tt>**USCXML_ELEM_X_IS_SET**</tt>: 

        These macros are defined for <tt>DATA</tt>, <tt>PARAM</tt> and
        <tt>DONEDATA</tt> and allow to iterate instances. For all of the
        corresponding SCXML elements, a callback might be supplied with a set
        of instances (e.g. <tt>invoke</tt> takes a set of <tt>&lt;param></tt>
        elements). They are contained in a continuous memory region and can be
        iterated by merely increasing the respective pointer. The macros allow
        to check whether the pointer is still valid or whether there are no
        more instances of the given structure.
      
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
    in user-supplied application code, the tranformation will define three
    additional macros:

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
a set of functions, you will need to allocate and clear memory for a
<tt>uscxml_ctx</tt> structure, set its machine field to a
<tt>uscxml_machine</tt> structure and register user-supplied callbacks.

### Context Callbacks

An SCXML interpreter does more than to perform a series of microsteps for an
event over a set of states and transitions and there are quite a few
responsibilities not implemented in the generated ANSI C code. These will be
delegated to user-supplied code via callbacks if they are required for the interpretation of a given SCXML file.

There is already a scaffolding providing most of the callbacks implemented in
the [test-c-machine.c](../test/src/test-c-machine.c) test file and you can just
isolate the <tt>StateMachine</tt> class contained within. It does everything
but custom invocations but requires linking with <tt>libuscxml</tt> for the
datamodel implementations and several other functions. Depending on the number
of SCXML language features you employ, you can get away with providing
considerably fewer callbacks as detailled below.

1. **Event Queues**:

    A compliant interpreter is required to maintain two event queues, an
    internal and an external one. These queues can grow to arbitrary size and
    we made a decision, not to employ <tt>malloc</tt> for heap allocations in
    the generated ANSI-C source. As such, it is the responsibility of the
    user-supplied code to manage the queues via the following callbacks:
    
    | Callback | Comments | Required For |
    |-|-|-|
    | <tt>**dequeue_internal**</tt> | This callback is invoked whenever the interpreter needs an event from the internal event queue. It is passed an instance of a <tt>uscxml_ctx</tt> structure and is supposed to return an opaque pointer to an event. If the internal queue is empty, <tt>NULL</tt> is to be returned. | Dequeuing *internal* events |
    | <tt>**dequeue_external**</tt> | This callback is functionally equivalent to <tt>uscxml_ctx.dequeue_internal</tt> but invoked, when an external event is to be dequeued. | Dequeuing *external* events |
    | <tt>**exec_content_send**</tt> | Whenever there is an <tt>&lt;send></tt> element encountered in executable content, the generated ANSI C code will invoke this callback with a context and an <tt>uscxml_elem_send</tt> instance and the user code registered at the callback is expected to handle the send request as per SCXML recommendation. | Delivering events via <tt>&lt;send></tt> |
    | <tt>**exec_content_raise**</tt> | This callback is invoked for any <tt>&lt;raise></tt> element processed as part of executable content and is expected to deliver an event to the internal event queue. | Delivering events via <tt>&lt;raise></tt> |
    
    The events themselves are represented as opaque pointers and the generated ANSI-C code will never access any of its members.
    
2. **Transition Matching / Enabling**

    An event will match and enable a set of transitions. The generated ANSI C
    source will already make sure that only valid sets of transitions can be
    selected to constitute the optimal transition set for a microstep, but
    user-supplied code will have to decide whether a transition is matched and
    enabled. 
    
    | Callback | Comments | Required For |
    |-|-|-|
    | <tt>**is_matched**</tt> | This callback receives a context, an <tt>uscxml_transition</tt> structure and the opaque event pointer. It is expected to return <tt>0</tt> for when the transition is not matched by the given event and <tt>1</tt> if it is. You can assume that non-spontaneous transitions are not checked for the null-event and vice versa. | Event name *matching* of a transition. |
    | <tt>**is_enabled**</tt> | This callback receives a context and a <tt>uscxml_transition</tt> structure. It is expected to return <tt>0</tt> for when the transition is not enabled and <tt>1</tt> if it is. Only transitions with an actual <tt>condition</tt> attribute will be checked. | Determining *enabled* status of a transition. |
    
3. **Invocations**

    The transformation will generate machine structures for all SCXML
    state-charts found within a document, but will make no attempt to invoke
    them automatically. Instead, the generated ANSI-C code will call upon the respective callback in the <tt>uscxml_ctx</tt> structure:
    
    | Callback | Comments | Required For |
    |-|-|-|
    | <tt>**invoke**</tt> | The call back is provided with a context and an <tt>uscxml_elem_invoke</tt> structure. This structure will contain all the information pertaining to the <tt>&lt;invoke></tt> element, with an additional optional member <tt>machine</tt>, which points to the <tt>uscxml_machine</tt> structure in case another, nested SCXML machine is to be invoked. It is your responsibility to create a <tt>uscxml_ctx</tt> for this new machine and run it or start any other type of invocation specified in the given structure. | Invoking external components via <tt>&lt;invoke></tt> |

4. **Executable Content**

    In general, every instance of an element for executable content has a respective callback in the <tt>uscxml_ctx</tt> structure. There are a few examples, wherein an element is transformed onto control flow that will invoke multiple callbacks:

    | Callback | Comments | Required For |
    |-|-|-|
    | <tt>**exec_content_log**</tt> | | <tt>&lt;log></tt> |
    | <tt>**exec_content_raise**</tt> | | <tt>&lt;raise></tt> |
    | <tt>**exec_content_send**</tt> | | <tt>&lt;send></tt> |
    | <tt>**is_true**</tt> | | <tt>&lt;if> / &lt;elseif> / &lt;else></tt> |
    | <tt>**exec_content_foreach_init**</tt> <tt>**exec_content_foreach_next**</tt> <tt>**exec_content_foreach_done**</tt> | | <tt>&lt;foreach></tt> |
    | <tt>**exec_content_assign**</tt> | | <tt>&lt;assign></tt> |
    | <tt>**exec_content_init**</tt> | | <tt>&lt;data></tt> |
    | <tt>**exec_content_cancel**</tt> | | <tt>&lt;cancel></tt> |
    | <tt>**exec_content_script**</tt> | | <tt>&lt;script></tt> |

5. **Done Events**

    Finally, there is a callback that is invoked if a <tt>&lt;final></tt> state is entered.

    | Callback | Comments | Required For |
    |-|-|-|
    | <tt>**raise_done_event**</tt> | The callback is provided with a context, the state for which a done event is to be raised and a <tt>uscxml_elem_donedata</tt> structure. | <tt>&lt;final></tt> |


### Inline SCXML

An alternative to writing an external SCXML file is to embed the document into the actual C code as a comment:

    /** INLINE SCXML BEGIN
    <scxml name="test-inline" datamodel="native">
    	<state id="foo">
    		<onentry>
    			enteredFoo();
    		</onentry>
    	</state>
    </scxml>
    INLINE SCXML END */ 

If you pass an arbitrary input file to <tt>uscxml_transform</tt>, it will realize that it does not constitute a proper SCXML document and attempt to isolate an actual SCXML state-chart by searching for the string literals <tt>INLINE SCXML BEGIN</tt> and <tt>INLINE SCXML END</tt>. Everything in between is isolated and treated as if it was a proper SCXML document.

Here, you can also see a variation with the <tt>datamode="native"</tt> attribute. If this is given, the transformation will write any text child of executable content as an unescaped, verbatim string literal into the respective function, allowing you to address any of your C functions and variables directly.