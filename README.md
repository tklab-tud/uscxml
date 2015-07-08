# uSCXML ReadMe

[![Build Status](https://travis-ci.org/sradomski/uscxml.png?branch=master)](https://travis-ci.org/sradomski/uscxml)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**

- [General](#general)
    - [Test Reports](#test-reports)
    - [License](#license)
    - [Download](#download)
- [Getting Started](#getting-started)
- [Advanced Topics](#advanced-topics)
    - [Embedding uSCXML](#embedding-uscxml)
    - [Extending uSCXML](#extending-uscxml)
- [Miscellaneous](#miscellaneous)
- [Acknowledgments](#acknowledgments)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

#### Related Documents

- [Building form Source](docs/BUILDING.md)
- [Developer Overview](docs/OVERVIEW.md)

## General

uSCXML is a SCXML interpreter written in C/C++. It is [standards compliant](#test-reports) and [easily extended](#extending-uscxml)
even in C# and Java. It runs on <b>Linux</b>, <b>Windows</b>, <b>Raspberry Pi</b> and <b>Mac OSX</b>, each 32- as well as 64Bits as well as <b>iOS</b>.

* <b>Data Models</b>
    * Full [ECMAScript data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/ecmascript) using Google's v8 (and JavaScriptCore on MacOSX and iOS)
        * Simplified support for [Web Storage](http://www.w3.org/TR/2013/REC-webstorage-20130730/) in document.localStorage
        * Support for binary data via [TypedArrays](https://www.khronos.org/registry/typedarray/specs/latest/) (will not throw exceptions yet)
    * Full [NULL data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/null) with required <tt>In</tt> predicate
    * [Prolog data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/prolog/swi) using SWI prolog
    * Experimental [Promela data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/promela) for use
      with the [SPIN](http://spinroot.com/spin/whatispin.html) model-checker
    * Early support for a [Lua data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/lua)
    * Rudimentary support for [XPath data model](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/xpath)
* <b>Invokers</b>
    * <tt>scxml</tt>: Invoke a nested scxml interpreter
    * <tt>dirmon</tt>: Watches a directory for changes to files
    * <tt>scenegraph</tt>: Simplified 3D scenegraphs with custom markup
    * <tt>heartbeat</tt>: Periodically sends events
    * <tt>umundo</tt>: Subscribe to channels and publish events
    * [Many others](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/invoker)
* <b>DOM</b>
    * DOM Core Level 2 + XPath extensions available for ecmascript data model
    * Namespace aware to embed custom markup for special invokers
* <b>Communication</b>
    * Features the standard basichttp I/O processor
    * Features the required SCXML I/O processor
    * <b>No</b> DOM I/O processor
    * Early support for [WebSockets](http://datatracker.ietf.org/doc/rfc6455/)
    * Can actually respond to HTTP requests with data via &lt;response>
* <b>Language Bindings</b>
    * Java bindings
    * C# bindings
    * PHP module for apache and cli interpreter (discontinued)

### Test Reports

* We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. 
* Have a look at the [result](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml) for the various platforms.
* The manual and XPath specific tests are [excluded](https://github.com/tklab-tud/uscxml/blob/master/test/ctest/CTestCustom.ctest.in).

To run the tests yourself, you need to generate the build environment and pass <tt>-DBUILD_TESTS=ON</tt> via CMake:

    $ cmake -DBUILD_TESTS=ON <USCXML_SRC> && make

Afterwards, you can run the various tests. There are more than 1500 tests in total, so maybe restrict yourself to 
some subset.

*W3C Tests ECMAScript Datamodel*

    $ ctest -L "^ecma/test"
    [...]
    $ 100% tests passed, 0 tests failed out of 196

*W3C Tests XPath Datamodel*

    $ ctest -L "^xpath/test"
    [...]
    $ 51% tests passed, 104 tests failed out of 211

*W3C Tests PROMELA Datamodel*

    $ ctest -L "^promela/test"
    [...]
    $ 89% tests passed, 18 tests failed out of 165

*W3C Tests Lua Datamodel*

    $ ctest -L "^lua/test"
    [...]
    $ 78% tests passed, 45 tests failed out of 201


### License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

### Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md).

## Getting Started

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

<!--
| Extension | Owned By | Remarks |
| ----------|----------|---------|
| <tt>DataModel</tt> | Interpreter | Register whole new classes via <tt>Factory::registerDataModel</tt>, ad-hoc data models for a specific interpreter instance via <tt>interpreter.setDataModel</tt>.    |
| <tt>DataModelExtension</tt>  | User        |      |
| <tt>Invoker</tt>   | Interpreter |      |
| <tt>IOProcessor</tt>        | Interpreter |      |
| <tt>ExecutableContent</tt>   | Interpreter |      |
| <tt>InterpreterMonitor</tt>  | User        |      |
-->
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

# Miscellaneous 

## Ad-hoc extensions are deallocated by their interpreter

If you register any ad-hoc extension with an interpreter, be it in C++ or a language binding, this extension's
instance <emph>belongs</emph> to the interpreter. This means i.e. that (i) the interpreter's destructor will
deallocate the extension instance, (ii) you cannot reuse it for another interpreter and (iii) you may not call
its destructor.

For the language bindings, this means furthermore that you have to call <tt>swigReleaseOwnership()</tt> on the
extension instance to prevent the target language's memory managment form calling the instances C++ native
destructor. The destructor can only be called once and the interpreter's destructor will do it.

If allocating additional extension instances per interpreter is expensive, consider using aggregation as a "has a"
relationship with the expensive part.

## Not all exceptions are propagated into the target languages

Only exceptions raised during the following methods are propagated into the target language:

    Interpreter::fromXML
    Interpreter::fromURI
    Interpreter::step
    Interpreter::interpret

If you dig around in the exposed APIs, there are other methods that may raise exceptions (e.g.
<tt>interpreter.getDataModel().eval()</tt>). Be careful when calling these. Ultimately, all exceptions ought to be
propagated into the target language to be handled accordingly. We are currently evaluating different approaches to
do so.

## Where is the Android Port?

When I originally tried to compile the required libraries for uSCXML on Android (libevent, curl, libxml2), it would
not work out of the box and I postponed. If there is a demand for an Android port, I can have another look. uSCXML
itself is written in a subset of C++99 and ought to compile just fine.

## UTF8 support

Currently, we use <tt>std::string</tt> to represent all strings. This is not a problem as e.g. the ECMAScript
data models will just interpret these as character arrays and handle Unicode respectively. Though it is a problem if
you like to use non-ASCII characters e.g. in the <tt>id</tt> attribute of states.

## Performance

The performance of uSCXML depends on many things like the employed data model and the platform it runs on. Using a
MacBook Pro with an Intel i7 @2.4Ghz and the ECMAScript data model (<tt>test/uscxml/test-performance.scxml</tt>), we
achieve about 20.000 events/sec. On a Raspberry Pi, however, only 350 events/sec are achieved.

If performance ought to be increased further, the first place to look would be most likely the employed DOM
implementation, which uses the rather expensive <tt>dynamic_cast</tt> somewhat too liberally. For a real
performance boost, the explicit SCXML DOM representation at runtime might be dropped in favor of some simple
structs representing the states and transitions. This has been no priority for us so far as even 350 events/sec is
plenty for our use-cases.

## What about some code documentation?

Up until recently, the APIs of uSCXML were still subject to rather substantial changes. If there is one thing worse
than no documentation, it is wrong documentation, so we did not document the source. Another stumbling block was the
fact that documentation would not show up in the language bindings.

Both issues are resolved by now: The APIs have not changed substantially in about 8 month and the new version of SWIG
will allow doxygen comments to be show up in various target languages; so we will document somewhen soon.

# Acknowledgments

This SCXML interpreter is developed at the [Telekooperation Group](http://www.tk.informatik.tu-darmstadt.de) of the Technical University of Darmstadt as part of the [SmartVortex](http://smartvortex.eu) project funded by the [7th European framework program](http://ec.europa.eu/research/fp7/index_en.cfm).