# uSCXML ReadMe

[![Build Status](https://travis-ci.org/tklab-tud/uscxml.png?branch=master)](https://travis-ci.org/tklab-tud/uscxml)[![Build status](https://ci.appveyor.com/api/projects/status/b3mwo7w2qhtjal6f/branch/master?svg=true)](https://ci.appveyor.com/project/sradomski/uscxml/branch/master)

**Note**: We deprecated the [old version](https://github.com/tklab-tud/uscxml/tree/legacy-1.0) and refactored quite a few classes and interfaces.

**Note**: Some of the features described below may not yet have made it into the new version, but all will eventually. If implied functionality is not yet available just post an issue and we will make it a priority.

## What is it?

uSCXML is a platform to work with state-charts given as
[SCXML](http://www.w3.org/TR/scxml/) files. Currently, it consists of three principal components:

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

### On the Command-line
    # interpret state-chart from url
    $ uscxml-browser https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml

### For Transformations
    # transform given SCXML document into ANSI-C fragment
    $ uscxml-transform -tc -i https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml
