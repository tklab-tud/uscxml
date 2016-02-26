# uSCXML ReadMe

[![Build Status](https://travis-ci.org/tklab-tud/uscxml.png?branch=master)](https://travis-ci.org/tklab-tud/uscxml)

#### Related Documents

- [Building from Source](docs/BUILDING.md)
- [Open Issues](docs/ISSUES.md)
- [Getting Started](docs/GETTING_STARTED.md)
- [Publications](docs/PUBLICATIONS.md)

## General

uSCXML is a SCXML interpreter and transformer written in C/C++. It is
[standards compliant](#test-reports) and [easily extended](#extending-uscxml)
even in C# and Java. The *interpreter* itself runs on <b>Linux</b>,
<b>Windows</b>, <b>Raspberry Pi</b> and <b>Mac OSX</b>, each 32- as well as
64Bits as well as <b>iOS</b>. The *generated native code* transformed from an
SCXML document runs on virtually any platform.

### Interpreter

The implementation of the SCXML **runtime interpreter** is available in the
<tt>libuscxml</tt> library with the <tt>uscxml-browser</tt> binary as a
frontend. It implements the following features:

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
* <b>Interactive Debugger</b>
    * Accessible via a [web-frontend](http://htmlpreview.github.io/?apps/uscxml-debugger.html)
    * Complete with user-defined breakpoints, data model inspection and stepping

### Transformer

The **transformer** is implemented in the <tt>libuscxml_transform</tt> library and
made available via the <tt>uscxml-transform</tt> binary. It is a general tool
for SCXML documents and currently implements the following features:

* Transformations onto
    * [Flattened SCXML documents](src/uscxml/transform/ChartToFlatSCXML.cpp) in which only a single state is ever active 
        * Resulting documents require slight adaptations to a compliant interpreter for donedata, the <tt>In</tt> predicate and invokers.
        * Semantic equivalence is shown via IRP tests.
    * [ANSI C native code](src/uscxml/transform/ChartToC.cpp) for easy embedding of SCXML state-charts in C and C++ programs
        * No custom I/O processors implemented in scaffolding just yet.
        * To get started with transforming and embedding ANSI C code, read the [inline SCXML document](docs/NATIVE_CODE.md).
    * [PROMELA programs](src/uscxml/transform/ChartToPromela.cpp) for model-checking via linear temporal logic with the SPIN model-checker.
        * Only defined for the <tt>promela</tt> and <tt>null</tt> datamodel.
    * [Minimized SCXML documents](src/uscxml/transform/ChartToMinimalSCXML.cpp) with dead states and executable content removed
        * Minimization is performed dynamically by marking elements as visited and removing unvisited elements.
* Annotations of the transitions exit set entry set, priority, conflicts, domain

Currently, we support a transformation from SCXML onto ANSI C. 

### Test Reports

* We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. 
* Some tests are [excluded](test/ctest/CTestCustom.ctest.in).

To run the tests yourself, you need to generate the build environment and pass <tt>-DBUILD_TESTS=ON</tt> via CMake:

    $ cmake -DBUILD_TESTS=ON <USCXML_SRC> && make

Afterwards, you can run the various tests. There are more than 3500 tests in total, 
so maybe restrict yourself to some subset.

|               | ECMAScript       | XPath            | PROMELA          | Lua              | Invoke as        |
|---------------|------------------|------------------|------------------|------------------|------------------|
| Plain IRP     | <tt>196/196</tt> | <tt>107/211</tt> | <tt>147/181</tt> | <tt>165/201</tt> | <tt>$ ctest -L "^[datamodel]/test"</tt> |
| Flattened IRP | <tt>196/196</tt> | <tt>107/211</tt> | <tt>147/181</tt> | <tt>165/201</tt> | <tt>$ ctest -L "^fsm/[datamodel]/test"</tt> |
| Generated C   | <tt>180/196</tt> | <tt>73/211</tt>  | <tt>144/181</tt> | <tt>143/201</tt> | <tt>$ ctest -L "^gen/c/[datamodel]/test"</tt>
| Verification  |                  |                  | <tt>130/181</tt> |                  | <tt>$ ctest -L "^spin/promela/test"</tt>


### License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](docs/BUILDING.md#build-dependencies) as well.

## Performance

We did some performance measurements in the scope of the C transformation. As
you can see in the figure below, for most IRP tests we average to a duration of
5-20us per microstep on an early 2015 MacBook Pro 13" with 3.1GHz in the case
of [generated/compiled C](test/src/test-c-machine.machine.c). For interpretation at runtime, we average at around 70-130us per
microstep. The generated C is rather optimized while the focus of the
interpreter is more on correctness, feature completeness and extensibility.
However, there are some lessons learned that are yet to be applied for the
interpreter.

<img src="https://raw.github.com/tklab-tud/uscxml/master/docs/Performance_Microstep.png" width="500px" />

For the tests, we took the 
[highest precision timer](src/uscxml/concurrency/Timer.cpp) 
we could attain and measured how long the execution of a given SCXML IRP test
took while subtracting initialization, tear-down and the time spent in the
data-model's routines. Time is averaged over 1.000 iterations.
