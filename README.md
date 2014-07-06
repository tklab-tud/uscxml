# uSCXML ReadMe

[![Build Status](https://travis-ci.org/sradomski/uscxml.png?branch=master)](https://travis-ci.org/sradomski/uscxml)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**

- [General](#general)
    - [Test Reports](#test-reports)
    - [License](#license)
    - [Download](#download)
- [Usage](#usage)
    - [Non-Blocking Interpretation with SCXML from URL](#non-blocking-interpretation-with-scxml-from-url)
    - [Blocking Interpretation with inline SCXML](#blocking-interpretation-with-inline-scxml)
    - [Interleaved Interpretation with inline SCXML](#interleaved-interpretation-with-inline-scxml)
    - [Callbacks for an Interpreter](#callbacks-for-an-interpreter)
- [Advanced Topics](#advanced-topics)
    - [Embedding uSCXML](#embedding-uscxml)
    - [Extending uSCXML](#extending-uscxml)
- [Acknowledgments](#acknowledgments)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## General

uSCXML is a SCXML interpreter written in C/C++. It is [standards compliant](#test-reports) and [easily extended](#extending-uscxml)
even in C# and Java. It runs on <b>Linux</b>, <b>Windows</b> and <b>Mac OSX</b>, each 32- as well as 64Bits as well as <b>iOS</b>.

* <b>Datamodels</b>
    * Full [ECMAScript datamodel](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/ecmascript) using Google's v8 (and JavaScriptCore on MacOSX and iOS)
        * Simplified support for [Web Storage](http://www.w3.org/TR/2013/REC-webstorage-20130730/) in document.localStorage
        * Support for binary data via [TypedArrays](https://www.khronos.org/registry/typedarray/specs/latest/) (will not throw exceptions yet)
    * Full [NULL datamodel](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/null) with required <tt>In</tt> predicate
    * [Prolog datamodel](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/prolog/swi) using SWI prolog
    * Early [Promela datamodel](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/promela) for use
      with the [SPIN](http://spinroot.com/spin/whatispin.html) model-checker
    * Rudimentary support for [XPath datamodel](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/datamodel/xpath)
* <b>Invokers</b>
    * <tt>scxml</tt>: Invoke a nested scxml interpreter
    * <tt>dirmon</tt>: Watches a directory for changes to files
    * <tt>scenegraph</tt>: Simplified 3D scenegraphs with custom markup
    * <tt>heartbeat</tt>: Periodically sends events
    * <tt>umundo</tt>: Subscribe to channels and publish events
    * [Many others](https://github.com/tklab-tud/uscxml/tree/master/src/uscxml/plugins/invoker)
* <b>DOM</b>
    * DOM Core Level 2 + XPath extensions available for ecmascript datamodel
    * Namespace aware to embed custom markup for special invokers
* <b>Communication</b>
    * Features the standard basichttp io-processor
    * Features the required SCXML io-processor
    * <b>No</b> DOM io-processor
    * Early support for [WebSockets](http://datatracker.ietf.org/doc/rfc6455/)
    * Can actually respond to HTTP requests with data via &lt;response>
* <b>Language Bindings</b>
    * PHP module for apache and cli interpreter
    * Java bindings

### Test Reports

* We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. 
* Have a look at the [result](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml) for the various platforms.
* The manual and XPath specific tests are [excluded](https://github.com/tklab-tud/uscxml/blob/master/contrib/ctest/CTestCustom.ctest.in).

uSCXML still fails the following ecmascript tests:

<table>
	<tr><th>Test#</th><th>Status</th><th>Description</th><th>Comment</th></tr>
	<tr>
		<td><tt>
			<a href="https://github.com/tklab-tud/uscxml/blob/master/test/w3c/ecma/test326.scxml">326</a> /
			<a href="https://github.com/tklab-tud/uscxml/blob/master/test/w3c/ecma/test326.scxml">329</a>
		</tt></td>
		<td><tt>Failed for v8</tt></td>
		<td>"test that _ioprocessors stays bound till the session ends" / "test that none of the system variables can be modified"</td>
		<td>The v8 implementation will return a new <tt>_ioprocessor</tt> object for each access.</td>
	</tr>
	<tr>
		<td><tt><a href="https://github.com/tklab-tud/uscxml/blob/master/test/w3c/ecma/test579.scxml">579</a></tt></td>
		<td><tt>Failed</tt></td>
		<td>"Before the parent state has been visited for the first time, if a transition is executed that takes the history state as its target, the SCXML processor MUST execute any executable content in the transition after the parent state's onentry content and any content in a possible initial transition."</td>
		<td>Functionality was recently added and is not yet supported.</td>
	</tr>
</table>

### License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

### Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md).

## Usage

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

### Blocking Interpretation with inline SCXML
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    scxml.interpret(); // blocking

When using blocking interpretation, it is assumed that it is running on the main thread and
it will call <tt>runOnMainThread</tt> between stable configurations.

### Interleaved Interpretation with inline SCXML
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    InterpreterState state;
    do {
      state = interpreter.step(true); // boolean argument causes blocking or not
    } while(state > 0)

Using <tt>step</tt>, you can run a single macrostep of the interpreter and interleave
interpretation with the rest of your code.

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

1. DataModels as embedded scripting languages (e.g. ECMAScript, Prolog and XPath)
2. Invokers to represent external components that deliver and accept events (e.g. iCal, SceneGraph, DirectoryMonitor)
3. I/O-Processors to provide communication with external systems (e.g. BasicHTTP, SCXML).
4. Elements for Executable Content (e.g. &lt;respond>, &lt;fetch>, &lt;postpone>).

The basic approach to extend the interpreter is the same in all cases:

1. Write a class inheriting the abstract base class (e.g. <tt>DataModelImpl</tt>, <tt>InvokerImpl</tt>, <tt>IOProcessorImpl</tt>, <tt>ExecutableContentImpl</tt>).
2. Instantiate your class and register it as a prototype at the <tt>Factory</tt> via one of its static <tt>register*</tt> methods.
    1. You can register at the global Factory Singleton via <tt>Factory::register*(prototypeInstance)</tt>
    2. Or provide a new Factory instance to selected interpreters as an in-between.
3. Write an interpreter using your new functionality.

# Acknowledgments

This SCXML interpreter is developed at the [Telekooperation Group](http://www.tk.informatik.tu-darmstadt.de) of the Technical University of Darmstadt as part of the [SmartVortex](http://smartvortex.eu) project funded by the [7th European framework program](http://ec.europa.eu/research/fp7/index_en.cfm).