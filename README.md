# uSCXML ReadMe

[![Build Status](https://travis-ci.org/tklab-tud/uscxml.png?branch=master)](https://travis-ci.org/tklab-tud/uscxml)[![Build status](https://ci.appveyor.com/api/projects/status/b3mwo7w2qhtjal6f/branch/master?svg=true)](https://ci.appveyor.com/project/sradomski/uscxml/branch/master)[![Build status](https://scan.coverity.com/projects/11688/badge.svg)](https://scan.coverity.com/projects/tklab-tud-uscxml)[![Coverage Status](https://coveralls.io/repos/github/tklab-tud/uscxml/badge.svg?branch=master)](https://coveralls.io/github/tklab-tud/uscxml?branch=master)

#### Quick Links

- [Building from source](http://tklab-tud.github.io/uscxml/building.html)
- [Changes](docs/CHANGES.md)
- [Tests passed](test/w3c/TESTS.md)
- [Publications](docs/PUBLICATIONS.md)

## What is it?

uSCXML is a platform to work with state-charts given as
[SCXML](http://www.w3.org/TR/scxml/) files. It consists of three principal components:

 1. `libuscxml`: [C++ library](#embedded-as-a-library) containing an interpreter and accompanying functionality.

 2. `uscxml-browser`: A standards compliant [command-line interpreter](#on-the-command-line) of SCXML documents.
 
 3. `uscxml-transform`: A collection of [transformation](#for-transformations) implementations to transpile SCXML, e.g. onto ANSI-C and VHDL.

The status of the various datamodels, bindings and generators with regard to the [W3C IRP
tests](https://www.w3.org/Voice/2013/scxml-irp/) can be checked in the [test
table](test/w3c/TESTS.md).

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
    while(scxml.step() != uscxml::USCXML_FINISHED) {
      ...
    }

**Examples:**

* [uscxml-browser.cpp](https://github.com/tklab-tud/uscxml/blob/master/apps/uscxml-browser.cpp) (**C++**)
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
* [WaterPump.cxx](https://github.com/tklab-tud/uscxml/blob/master/apps/arduino/WaterPump.cxx) (**C++ on Arduino**)

## Benchmarks

We did conceive a [series of benchmarks](https://github.com/tklab-tud/uscxml/tree/master/test/benchmarks) SCXML documents to evaluate the performance of the various SCXML implementations. The state-charts in the benchmarks are completely artificial and bear no resemblance to real-world state-charts. However, they may provide a general guidance to get an impression about the performance of the different implementations.

The implementations each stress a specific feature of any SCXML `microstep(T)` implementation. Each contains a state `mark` that is continuously entered and exited as part of a sequence of spontaneous microsteps and measures the entries per second. For every implementation, the [benchmark is run](https://github.com/tklab-tud/uscxml/blob/master/contrib/benchmarks/run.sh) for a number of seconds and the iterations per seconds are averaged. The benchmarks exist in increasing complexity from very simple with, e.g., 4 states nested in a depth of 4 compounds up until 512 for state-charts with > 250.000 states.

**Note:** If you are the author / maintainer of one of the SCXML implementations being benchmarked below and feel that I misrepresent your implementation's performance, post an issue and I will set things straight.

**Note:** There are two `microstep(T)` implementations in uSCXML, namely `fast` and `large` with the former being the default for transpilation and the latter for interpretation. Both are being employed on an interpreted state-chart here. For the `fast` microstep implementation we measured the case with pre-calculated predicates.

**Note:** The numbers for scxmlcc are necessarily for the compiled case and N/A if we could not compile the state-chart within the time limit.

### Transitions

The Transitions benchmark measures transition selection with many conflicting transitions enabled as part of a microstep.

![Transition Benchmark](https://user-images.githubusercontent.com/980655/27858834-004c9c78-6177-11e7-8519-2f73f0ff9fb4.png)

### LCCA
When exiting a state via a transition, the least-common compound ancestor (LCCA) of the transition's targets and source state has to be identified. This is a common operation and its runtime is proportional to the nesting depth if implemented respectively.

![LCCA Benchmark](https://user-images.githubusercontent.com/980655/27858835-00527ecc-6177-11e7-85d2-46c83ad5ed71.png)

### Conclusion

uSCXML with either microstep implementation is consistently the fastest with the exception of the Transitions benchmark, where the compiled `scxmlcc` is degenerating slower for more complex state-charts. This may be due to compiler optimizations (or an incomplete implementation) and it would be interesting to compare `scxmlcc` against the transpiled ANSI-C code from `uscxml-transform`. However, the limiting factor here becomes the time required to transpile the state-chart or to compile the generated source file into an executable binary respectively. With regard to huge state-charts, the large microstep implementation of `uSCXML` performs best and retains acceptable performance throughout the range of benchmarks, only surpassed by the fast implementation for smaller complexities.

# Changes {#changes}

 * **[bfefa5fd44b9ed1491612f26b099db8ad624247b](https://github.com/tklab-tud/uscxml/pull/155/commits/bfefa5fd44b9ed1491612f26b099db8ad624247b):**

    We **broke the InterpreterMonitor** API by substituting the Interpreter instance in the first formal parameter by its sessionId throughout all callbacks. Retrieving the actual Interpreter involved locking a weak_ptr into a shared_ptr which proved to be a performance bottleneck. You can retrieve the Interpreter from its sessionId via the new static method `Interpreter::fromSessionId` if you actually need.

