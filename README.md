# uSCXML ReadMe

[![Build Status](https://travis-ci.org/tklab-tud/uscxml.png?branch=master)](https://travis-ci.org/tklab-tud/uscxml)[![Build status](https://ci.appveyor.com/api/projects/status/b3mwo7w2qhtjal6f/branch/master?svg=true)](https://ci.appveyor.com/project/sradomski/uscxml/branch/master)[![Build status](https://scan.coverity.com/projects/11688/badge.svg)](https://scan.coverity.com/projects/tklab-tud-uscxml)[![Coverage Status](https://coveralls.io/repos/github/tklab-tud/uscxml/badge.svg?branch=master)](https://coveralls.io/github/tklab-tud/uscxml?branch=master)

#### Quick Links

- [Building from source](http://tklab-tud.github.io/uscxml/building.html)
- [Tests passed](test/w3c/TESTS.md)
- [Publications](docs/PUBLICATIONS.md)
- [Benchmarks](docs/BENCHMARKS.md)

## What is it?

uSCXML is a platform to work with state-charts given as [SCXML](http://www.w3.org/TR/scxml/) files. It features the [fastest microstep](docs/BENCHMARKS.md) implementation available and consists of three principal components:

 1. `libuscxml`: [C++ library](#embedded-as-a-library) containing an interpreter and accompanying functionality.

 2. `uscxml-browser`: A standards compliant [command-line interpreter](#on-the-command-line) of SCXML documents.
 
 3. `uscxml-transform`: A collection of [transformation](#for-transformations) implementations to transpile SCXML, e.g. onto ANSI-C and VHDL.

The status of the various datamodels, bindings and generators with regard to the [W3C IRPtests](https://www.w3.org/Voice/2013/scxml-irp/) can be checked in the [test table](test/w3c/TESTS.md).

## Installation

There are no installers yet and we do not feature any releases. Just check for [open issues](https://github.com/tklab-tud/uscxml/issues) and [build from source](http://tklab-tud.github.io/uscxml/building.html). If you did download and build locally, you can create installers via `make packages` though.

## Documentation

Documentation is available at our [github pages](http://tklab-tud.github.io/uscxml/). It is created from inline comments in the source along with some dedicated markdown pages via `doxygen`. We try to keep it current and will update it ever again. For the most current documentation, you can run `make docs` in your build directory.

## Licensing

uSCXML itself is distributed under the [Simplified BSD license](http://www.opensource.org/licenses/bsd-license) as in, do not sue
us and do not misrepresent authorship. There are currently four additional libraries that are required to compile uSCXML.

| Project | License | Comment |
|---------|---------|---------|
| [libcurl](https://curl.haxx.se/libcurl/) | [MIT/X derivate](https://curl.haxx.se/docs/copyright.html) | Used in uSCXML to fetch remote content |
| [Xerces-C++](https://xerces.apache.org/xerces-c/) | [Apache v2](http://www.apache.org/licenses/LICENSE-2.0.html) | XML parser and DOM implementation |
| [libevent](http://libevent.org) | [3-clause BSD](http://libevent.org/LICENSE.txt) | Delayed event queues |
| [uriparser](http://uriparser.sourceforge.net) | [New BSD](https://sourceforge.net/p/uriparser/git/ci/master/tree/COPYING) | Referring and resolving URIs |

At configure time, the uSCXML build-process will attempt to find and link several other libraries (e.g. Lua, v8) and additional licensing terms may apply.

## Getting Started

For more detailled information, refer to the [documentation](http://tklab-tud.github.io/uscxml).

### Embedded as a Library
    uscxml::Interpreter scxml = uscxml::Interpreter::fromURL("...");
    scxml.on().enterState([](const std::string& sessionId,
                             const std::string& stateName,
                             const xercesc_3_1::DOMElement* state) {
        std::cout << "Entered " << stateName << std::endl;
    });

    while(scxml.step() != uscxml::USCXML_FINISHED) {
      ...
    }

**Examples:**

* [uscxml-browser.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/apps/uscxml-browser.cpp) (**C++**)
* [test-state-pass.cpp](https://github.com/tklab-tud/uscxml/blob/master/test/src/test-state-pass.cpp) (**C++**)
* [TestStatePass.cs](https://github.com/tklab-tud/uscxml/blob/master/contrib/csharp/bindings/TestStatePass.cs) (**C#**)
* [test-state-pass.py](https://github.com/tklab-tud/uscxml/blob/master/contrib/python/bindings/test-state-pass.py) (**Python**)
* [JexlDataModelTest.java](https://github.com/tklab-tud/uscxml/blob/master/contrib/java/bindings/org/uscxml/tests/JexlDataModelTest.java) (**Java**)


### On the Command-line
    # interpret state-chart from url
    $ uscxml-browser https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml

### For Transformations
    # transform given SCXML document into ANSI-C fragment
    $ uscxml-transform -tc -i https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml

**Examples:**

* [test-gen-c.cpp](https://github.com/tklab-tud/uscxml/blob/master/test/src/test-gen-c.cpp) (**C++**)
* [WaterPump.cxx](https://github.com/tklab-tud/uscxml/blob/master/examples/cpp/transpiled/arduino/WaterPump.cxx) (**C++ on Arduino**)


## Changes

 * **08/01/2017:**

    We selectively re-enabled support for Google's V8 ECMAScript engine, but only in version 3.23.17 and 3.14.05 and API compatible versions. These two versions are noteworthy as the first one used to be distributed via MacPorts and the second one is still found in many Linux distributions (e.g. Debian and Ubuntu). It is bordering on impossible to build them from source today as they are rather old. If you need an ECMAScript datamodel and do not have binary images of these, just go for `libjavascriptcoregtk-4.0-dev`. Make sure it's version **4.0** as the previous version had a bug with `JSCheckScriptSyntax`.

 * **07/19/2017:**

    We **dropped support for Google's V8 ECMAScript engine**. The API is changing too fast and there is no reliable way to get / build / identify older versions. The latest branch will not work with the wrappers generated from even SWIG 4.0 and I have no time to keep up with them. Use JavaScriptCore, its API is unchanged since we started to support it in 2012. If you feel capable to maintain the [](V8DataModel.cpp) send a push request. Everything will be left in place but we will ignore `libv8` at configure time. I may have another look when a number of Linux distribution settled on a more recent version, most are still shipping v8 in version 3.14.

 * **07/05/2017:**

    We **broke the InterpreterMonitor** API by substituting the Interpreter instance in the first formal parameter by its sessionId throughout all callbacks. Retrieving the actual Interpreter involved locking a weak_ptr into a shared_ptr which proved to be a performance bottleneck. You can retrieve the Interpreter from its sessionId via the new static method `Interpreter::fromSessionId` if you actually need.

