# Getting Started

In order to use the interpreter, you need to <tt>#include "uscxml/Interpreter.h"</tt> and instantiate
objects of <tt>uscxml::Interpreter</tt>.

### Non-Blocking Interpretation with SCXML from URL
    Interpreter scxml = Interpreter::fromURL("http://www.example.com/fancy.scxml");
    scxml.start(); // non-blocking in own thread

There are some cases, i.e. with graphical invokers, where the main thread is <emph>required</emph> in order
to react to UI events. You will have to deligate control flow from the main thread into the interpreter
every now and then:

    interpreter.runOnMainThread(25);

This will perform a single iteration on the invoked components with a maximum of 25 frames per seconds 
or return immediately. You will have to call this method every now and then if you are using e.g. the
<tt>scenegraph</tt> invoker.

<b>Note:</b> Running the interpreter in its own thread via <tt>start</tt> is not exposed into the 
language bindings. Just use the threading concepts native to your language to call <tt>step</tt> or 
<tt>interpret</tt> as outlined below.

### Blocking Interpretation with inline SCXML
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    scxml.interpret(); // blocking

When using blocking interpretation, it is assumed that it is running on the main thread and
it will call <tt>runOnMainThread</tt> between stable configurations.

### Interleaved Interpretation with inline SCXML
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    InterpreterState state;
    do {
      state = interpreter.step(ms);
    } while(state != InterpreterState::USCXML_FINISHED)

Using <tt>step</tt>, you can run a single macrostep of the interpreter and interleave
interpretation with the rest of your code. The <tt>step</tt> function will take an optional integer as
the time in milliseconds it will block and wait if no more events are available, default is to block
indefinitely until an event arrives or the interpreter finished.

### Callbacks for an Interpreter

You can register an <tt>InterpreterMonitor</tt> prior to start in order to receive
control-flow upon various events in the Interpreter.

    class StatusMonitor : public uscxml::InterpreterMonitor {
    	void onStableConfiguration(...)
    	void beforeCompletion(...)
    	void afterCompletion(...)
    	void beforeMicroStep(...)
    	void beforeTakingTransitions(...)
    	void beforeEnteringStates(...)
    	void afterEnteringStates(...)
    	void beforeExitingStates(...)
    	void afterExitingStates(...)
    };

    StatusMonitor statMon;
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    scxml.addMonitor(&statMon);
    scxml.start();

This will cause the interpreter to invoke the callbacks from the monitor whenever the corresponding
internal phase is reached.

## Advanced Topics

### Embedding uSCXML

There are bindings for [Java](https://github.com/tklab-tud/uscxml/tree/master/embedding/java) and 
[C#](https://github.com/tklab-tud/uscxml/tree/master/embedding/csharp) with some examples in the 
<tt>embedding</tt> directory. The bindings consist of two parts each 

1. The C++ uscxml interpreter compiled as a loadable module for the target language and 
2. A target language specific module (uscxml.jar / uscxmlCSharp.dll) with the wrapper classes. 

The first one is loaded by the target language (System.loadLibrary / SetDLLDirectory) while the second is to be
included in your actual project. Have a look at the examples in <tt>embedding</tt> and adapt the paths to reflect
your setup. See the [build instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md) for
details on how to build these.

### Extending uSCXML

The uSCXML interpreter can be extended by introducing new

1. Data models as embedded scripting languages (e.g. ECMAScript, Prolog and XPath)
2. Invokers to represent external components that deliver and accept events (e.g. iCal, SceneGraph, DirectoryMonitor)
3. I/O-Processors to provide communication with external systems (e.g. BasicHTTP, SCXML).
4. Elements for Executable Content (e.g. &lt;respond>, &lt;fetch>, &lt;postpone>).
5. Data model extionsions to establish callbacks from the data model into the host language.

The basic approach to extend the interpreter is the same in all cases:

1. Write a class inheriting the abstract base class (e.g. <tt>DataModelImpl</tt>, <tt>InvokerImpl</tt>, <tt>IOProcessorImpl</tt>, <tt>ExecutableContentImpl</tt>).
2. Instantiate your class and register it as a prototype at the <tt>Factory</tt> via one of its static <tt>register*</tt> methods.
    1. You can register at the global Factory Singleton via <tt>Factory::register*(prototypeInstance)</tt>
    2. Or provide a new Factory instance to selected interpreters as an in-between.
3. Write an interpreter using your new functionality.

<b>Note:</b> Within the language bindings, you will have to inherit the base classes without the <tt>Impl</tt>
suffix. Have a look at the examples in <tt>embedding</tt> for examples.

#### Ad-hoc Extensions

Sometimes, it is more suited to provide an interpreter with an already instantiated extension (e.g. an
IOProcessor with an existing connection). In this case, it is somewhat awkward to register a prototype and
have all initialization in its <tt>create(Interpreter interpreter)</tt> method. While you can still dispatch
over the interpreter instance and access information from some global Interpreter->Data map, there is a
more straight-forward approach, e.g. in Java:

    Interpreter interpreter = Intepreter.fromURI(uri);
    AdhocIOProcessor ioProc = new AdhocIOProcessor(Whatever youLike);
    ioProc.setParameter1(something);
    interpreter.addIOProcessor(ioProc);

This will cause the interpreter to use the given instance for all send requests targeting one of the types 
returned by <tt>ioProc.getNames()</tt> and not instantiate an instance via the factory. The instance can
deliver events into the interpreter via <tt>returnEvent(Event e, boolean toInternalQueue = false)</tt>. The same 
approach can be used for invokers:

    Interpreter interpreter = Intepreter.fromURI(uri);
    TestAdhocInvoker invoker1 = new TestAdhocInvoker(Whatever youLike);
    invoker1.setParameter1(something);
    interpreter.setInvoker("invokeId", invoker1);

This will cause the interpreter to use the given instance for a given <tt>invokeId</tt> and not instantiate via
the factory. Similarly, data models can be registered via <tt>interpreter.setDataModel(DataModel dm)</tt>.

<b>Note:</b> Providing ad-hoc extensions is only supported before the interpreter is started. If you change
instances with a running interpreter, the behavior is undefined.