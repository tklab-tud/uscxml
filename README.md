# uSCXML ReadMe

[![Build Status](https://travis-ci.org/sradomski/uscxml.png?branch=master)](https://travis-ci.org/sradomski/uscxml)

uSCXML is a SCXML interpreter written in C/C++. It is mostly feature-complete and to a large extend
[standards compliant](https://github.com/tklab-tud/uscxml#test-reports).
It runs on <b>Linux</b>, <b>Windows</b> and <b>MacOSX</b>, each 32- as well as 64Bits as well as <b>iOS</b>.
There are still a few rough edges though, especially with the plugins and custom extensions.

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

## Test Reports

* We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. 
* Have a look at the [result](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml) for the various platforms.
* The manual and XPath specific tests are [excluded](https://github.com/tklab-tud/uscxml/blob/master/contrib/ctest/CTestCustom.ctest.in).

uSCXML still fails the following ecmascript tests:

<table>
	<tr><th>Test#</th><th>Status</th><th>Description</th><th>Comment</th></tr>
	<tr>
		<td><tt><a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test329.scxml">329</a></tt></td>
		<td><tt>Failed</tt></td>
		<td>"test that none of the system variables can be modified"</td>
		<td>uSCXML allows writing to <tt>_event</tt>. This is very useful to have a scope 
			that vanishes when processing an event is finished. I raised the issue on the ML and it might make it into a later draft</td>
	</tr>
	<tr>
		<td><tt><a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test346.scxml">346</a></tt></td>
		<td><tt>Failed</tt></td>
		<td>"test that any attempt to change the value of a system variable causes error.execution to be raised"</td>
		<td>Same issue as above: we allow writing to <tt>_event</tt>.</td>
	</tr>
	<tr>
		<td>
			<tt>
				<a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test519.scxml">519</a>
				<a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test520.scxml">520</a>
				<a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test531.scxml">531</a>
				<a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test534.scxml">534</a>
			</tt></td>
		<td><tt>Failed</tt></td>
		<td></td>
		<td>Tests contain non-standard ECMAScript.</td>
	</tr>
</table>

## License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

## Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md).

## Usage

In order to use the interpreter, you need to <tt>#include "uscxml/Interpreter.h"</tt> and instantiate
objects of <tt>uscxml::Interpreter</tt>.

### Non-Blocking Interpretation with SCXML from URL
    Interpreter scxml = Interpreter::fromURL("http://www.example.com/fancy.scxml");
    scxml.start(); // non-blocking

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

### Callbacks for an Interpreter

You can register an <tt>InterpreterMonitor</tt> prior to start in order to receive
control-flow upon various events in the Interpreter.

    class StatusMonitor : public uscxml::InterpreterMonitor {
    	void onStableConfiguration(Interpreter) {}
    	void beforeCompletion(Interpreter) {}
    	void afterCompletion(Interpreter) {}
    	void beforeMicroStep(Interpreter) {}
    	void beforeTakingTransitions(Interpreter, const Arabica::XPath::NodeSet<std::string>&) {}
    	void beforeEnteringStates(Interpreter, const Arabica::XPath::NodeSet<std::string>&) {}
    	void afterEnteringStates(Interpreter) {}
    	void beforeExitingStates(Interpreter, const Arabica::XPath::NodeSet<std::string>&) {}
    	void afterExitingStates(Interpreter) {}
    };

    StatusMonitor statMon;
    Interpreter scxml = Interpreter::fromXML("<scxml><final id="exit"/></scxml>");
    scxml.addMonitor(&statMon);
    scxml.start();

This will cause the interpreter to invoke the callbacks from the monitor whenever the corresponding
internal phase is reached.

## Extending uSCXML

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