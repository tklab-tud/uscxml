# Building from Source {#building}

<!-- https://sourceforge.net/p/doxygen/discussion/markdown_syntax -->

[TOC]

This page describes how to build uSCXML from source, starting with either a git
checkout or from a downloaded archive. The source code is built using CMake and
the process of building uscxml is essentially the same on every platform.

1. Read the <b>[Platform Notes](#platform-notes)</b> below to prepare your system.
2. Checkout uscxml into a convenient directory.
3. Create a new directory for an *out-of-source* build. I usually create sub-directories in <tt>&lt;USCXML_SRC&gt;/build/</tt>.
4. Run cmake (or ccmake / CMake-GUI) to create the files required by your actual build-system.
5. Use your actual build-system or development environment to build uscxml.
6. Optionally build the [language bindings](#language-bindings) to embed the SCXML interpreter in another language.
7. Read the SCXML draft and have a look at the tests to get started.

For **Makefiles on Unices**, these steps essentially boil down to:

	$ git clone git://github.com/tklab-tud/uscxml.git
	$ mkdir uscxml/build && cd uscxml/build
	$ cmake .. && make

For **MSVC on Windows**, run form a developer command-prompt and substitute the last line above by:

	$ cmake -G "NMake Makefiles" .. && nmake

<b>Note:</b> If you want to build for another IDE or build-system, just create
a new *out-of-source* build directory and start over with CMake. To get an idea
of supported IDEs and build-environments on your platform, type <tt>cmake
--help</tt> or run the CMake-GUI and look for the *Generators* section at the
end of the output.

<b>Note:</b> If you plan to use the Eclipse CDT generator, you cannot have a
build directory anywhere under the source directory - just create the build
directory anywhere else. This only applies to the Eclipse CDT project generator.

<b>Note:</b> I could not build the language bindings with the Visual Studio
generator as it croaks when calling SWIG, just have another build directory
with the "NMake Makefiles" project generator.

<b>Note:</b> In order to compile with `MinGW` on windows you will have to adapt the build scripts in `contrib/cmake/Build*`. If you succeed, a pull request would be most appreciated.


\section deps Build Dependencies

Overview of the uSCXML dependencies. See the [Platform Notes](#platform-notes) for details.

<b>Note:</b> We no longer maintain and download pre-compiled versions of the dependencies at configure-time. Instead, the build process is using [<tt>external_project_add</tt>](http://www.kitware.com/media/html/BuildingExternalProjectsWithCMake2.8.html) to download and compile the required dependencies on your machine.

<table>
    <tr><th>Platform</th><th>Dependency</th><th>Version</th><th>Comment</th></tr>
	<tr>
		<td rowspan="7"><b>Everyone</b></td>
			<td><a href="https://cmake.org/download/">CMake</a><br>required</td>
			<td>>=&nbsp;2.8.6</td>
			<td>The build-system used for uSCXML.</td>
		</tr>
		<tr>
			<td><a href="http://libevent.org">libevent</a><br>required / auto-build</td>
			<td>>=&nbsp;2.0.22</td>
			<td>Delayed event queues with timed callbacks and the HTTP server.</td>
		</tr>
		<tr>
			<td><a href="http://curl.haxx.se">curl</a><br>required / auto-build</td>
			<td>>=&nbsp;7.48.0</td>
			<td>URL downloads.</td>
		</tr>
		<tr>
			<td><a href="https://github.com/jezhiggins/arabica">Xerces-C++</a><br />required / auto-build</td>
			<td>>=&nbsp;3.1.3</td>
			<td>XML Document Object Model</td>
		</tr>
		<tr>
			<td><a href="http://uriparser.sourceforge.net">uriparser</a><br />required / auto-build</td>
			<td>>=&nbsp;0.8.4</td>
			<td>URL resolving, referring and other operations</td>
		</tr>
		<tr>
			<td><a href="http://www.swig.org">SWIG</a><br />optional</td>
			<td>>=&nbsp;2.0.6</td>
			<td>Generates language bindings to embed uSCXML in other target languages.</td>
		</tr>
		<tr>
			<td><a href="http://www.stack.nl/~dimitri/doxygen/">Doxygen</a><br />optional</td>
			<td>>=&nbsp;1.8</td>
			<td>Used by <tt>make docs</tt> to generate this documentation from source comments.</td></tr>
	</tr>
	<tr bgcolor="grey" height="0.5em"><td bgcolor="#dddddd" colspan="4"></td></tr>
	<tr>
		<td rowspan="2"><b>Mac OSX</b></td>
			<td><a href="http://developer.apple.com/xcode/">XCode</a><br />required</td>
			<td>4.2 works</td>
			<td>Apple's SDK with all the toolchains.</td>
		</tr>
		<tr>
			<td><a href="http://www.macports.org/">MacPorts</a><br />recommended</td>
			<td>>=&nbsp;2.0.3</td>
			<td>Build system for a wide selection of open-source packages.</td>
		</tr>
	</tr>

	<tr>
		<td rowspan="1"><b>Linux</b></td>
			<td><a href="https://gcc.gnu.org">gcc</a> / <a href="http://clang.llvm.org">clang</a><br />required</td>
			<td>>=&nbsp;4.8 / 3.3</td>
			<td>C++ compiler with sufficient C++11 support.</td></tr>
	</tr>

	<tr>
	<td rowspan="1"><b>Windows</b></td>
		<td><a href="http://www.microsoft.com/visualstudio/en-us">Visual&nbsp;Studio / MSVC</a><br />required</td>
		<td>>=&nbsp;2012</td>
		<td>You *need* a C++ compiler that understands C++11.</td></tr>
	</tr>
</table>

\subsection optional-functionality Optional Functionality

At configure time, CMake will search for various libraries and conditionally
compile only those components of uSCXML for which respective libraries have been found (e.g. the Lua or ECMAScript data-model implementations). On unices, it is straight forward to add libraries and CMake will usually pick them up. 

On Windows, however, the process is more complicated. We primarily rely on the official CMake Modules to find the header files and libraries for various packages. This will, usually, take the file system destinations of popular installers into account. When you have trouble getting CMake to find some particular library, have a look at the <tt>Find*</tt> modules from the CMake distribution and the modules distributed with uSCXML in <tt>contrib/cmake/</tt> to get an idea where the files are expected.

\section platform-notes Platform Notes

The following sections will detail the preparation of the respective platforms to ultimately compile uscxml.

\subsection macosx Mac OSX

You will have to install <tt>CMake</tt> via Macports:

	# required dependencies
	$ sudo port install cmake
	
	# optional dependencies for language bindings
	$ sudo port install apache-ant swig-java swig-php swig-csharp

	# other optional dependencies
	$ sudo port install lua v8

The rest is pre-installed or downloaded and built at configure-time. Just
download the source and invoke CMake to create Makefiles or a Xcode project.

\subsubsection console-make Console / Make

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the uscxml-browser with a test.scxml file:

	$ ./bin/uscxml-browser ../../test/w3c/null/test436.scxml

\subsubsection xcode Xcode

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/xcode && cd build/xcode
	$ cmake -G Xcode ../..
	[...]
	-- Build files have been written to: .../build/xcode
	$ open uscxml.xcodeproj

You can of course reuse the same source directory for many build directories.

\subsection linux Linux

Depending on your distribution, you will most likely have apt-get or yum
available as package managers. If you do not, I'll have to assume that you are
knowledgable enough to resolve build dependencies on your own.

<b>Note:</b> If you need the ECMAscript
data-model, we advise to use one of the <tt>javascriptcoregtk</tt>
packages as the JavaScriptCore API is far more stable than V8. uSCXML will build with version 3.23 of V8 as it is currently distributed with MacPorts.

\subsubsection apt-get Preparing apt-get based distributions

This would be all distributions based on Debian, like Ubuntu, Linux Mint and the like.

	# build system and compiler
	$ sudo apt-get install git cmake cmake-curses-gui make g++

	# uscxml required dependencies (built if not installed)
	$ sudo apt-get install libxerces-c-dev libevent-dev libcurl4-openssl-dev

	# optional dependencies for language bindings
	$ sudo apt-get install ant swig liblua5.2-0-dev mono-devel


There may still be packages missing due to the set of dependencies among
packages in the various distributons. Try to run CMake and resolve dependencies
until you are satisfied.

\subsubsection yum Preparing yum based distributions

This would be all distributions based on Redhat, e.g. Fedora.

	# build system and compiler
	$ sudo yum install git cmake cmake-gui gcc-c++

	# uscxml required dependencies
	$ sudo yum install xerces-c-devel libevent-devel libcurl-devel

\subsubsection console-make2 Console / Make

Instructions are a literal copy of building uscxml for MacOSX on the console from above:

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the uscxml-browser with a test.scxml file:

	$ ./bin/uscxml-browser ../../test/w3c/null/test436.scxml

\subsubsection eclipse-cdt Eclipse CDT

<b>Note:</b> Eclipse does not like the project to be a subdirectory in the
source. You have to choose your build directory with the generated project
accordingly.

	$ mkdir -p ~/Desktop/build/uscxml/eclipse && cd ~/Desktop/build/uscxml/eclipse
	$ cmake -G "Eclipse CDT4 - Unix Makefiles" <USCXML_SRCDIR>
	[...]
	-- Build files have been written to: .../build/uscxml/eclipse

Now open Eclipse CDT and import the out-of-source directory as an existing project into workspace, leaving the "Copy projects
into workspace" checkbox unchecked. There are some more [detailed instruction](http://www.cmake.org/Wiki/Eclipse_CDT4_Generator) available
in the CMake wiki as well.

\subsection windows Windows

Building from source on windows is somewhat more involved and instructions are
necessarily in prose form. These instructions were created using Windows 7 and
MS Visual Studio 2012.

\subsubsection prepare-windows Prepare compilation

1. Use git to **checkout** the source from <tt>git://github.com/tklab-tud/uscxml.git</tt>
	into any convenient directory. 

2. Start the **CMake-GUI** and enter the checkout directory in the "Where is the source code" text field. Choose any convenient directory to build the binaries in.

3. Hit **Configure** and choose your toolchain and compiler - I only tested with Visual Studio 12. Hit **Configure** again until there are no more red items in the list. If these instructions are still correct and you did as described above, you should be able to "Generate" the Visual Project Solution.

Now you can generate the MS Visual Studio project file <tt><USCXML_BUILDIR>/uscxml.sln</tt>.
Just open it up to continue in your IDE.

<b>Note:</b> We only tested with the MSVC compiler. You can try to compile
with MinGW but you would have to conditionalize the [build scripts](https://github.com/tklab-tud/uscxml/tree/master/contrib/cmake) for e.g. MinGW.

<!--
\subsection ios iOS

We provide prebuilts and CMake toolchain files for iOS and the iOS simulator. The easiest way to get iOS binaries is
to run:

	$ pwd
	<USCXML_SRC>
	$ ./contrib/build-scripts/build-uscxml-ios.sh

This will build uSCXML with the latest iOS SDK that is installed on your system. If you prefer an older SDK, you can
<tt>export IOS_SDK_VERSION=6.1</tt> but you have to make sure it's actually installed. Have a look at the build
script and the toolchain files at <tt>contrib/cmake/CrossCompile-*</tt> if you run into issues.

The build script above will build a universal binary for simulator and device, both in release and debug configuration.
If you just want a specific configuration for e.g. the simulator, you can invoke CMake yourself:

	$ pwd
	<USCXML_SRC>
	$ mkdir build/iossim && cd build/iossim
	$ cmake -DCMAKE_TOOLCHAIN_FILE=../../contrib/cmake/CrossCompile-iOS-Sim.cmake ../..
	$ make -j4 

<b>Note</b>: We did not compile the prebuilts for iOS with 64Bit yet. As such, you will not get binaries build for
arm64. The main culprit is, again, curl which assumes the size of an int to be the identical.
-->

\subsection raspberry Raspberry Pi

To compile uSCXML on Raspberry Pi you will need to, at a minimum, install the following packages. This assumes that
you run Raspberry, the Debian variant.

	$ sudo apt-get install cmake libxerces-c libcurl4-gnutls-dev

Now you can compile uSCXML like on any other platform:

	$ git clone --depth 1 https://github.com/tklab-tud/uscxml.git
	$ mkdir -p uscxml/build/raspberry && cd uscxml/build/raspberry
	$ cmake ../..
	$ make

If you want an ECMAScript datamodel or LUA, you will need to install additional packages:

	# additional datamodels: ECMAScript, LUA
	$ sudo apt-get install libjavascriptcoregtk-3.0-dev liblua5.2-dev

Finally, to get the language bindings install SWIG and the developer kits of
the respective language. Older Java versions will work as well (>= 1.5), just
make sure <tt>JAVA_HOME</tt> is set correctly.

	# language bindings: Java, CSharp
	$ sudo apt-get install swig ant oracle-java8-jdk mono-mcs
	$ echo $JAVA_HOME
	/usr/lib/jvm/jdk-8-oracle-arm-vfp-hflt

\section language-bindings Language Bindings

In order to build any language bindings, you will need to have SWIG and the development kit of your target language
installed. The set of available language bindings is printed at the end of the CMake invocation:

	$ cmake <USCXML_SRC>
	...
	--   Available custom elements ...... : respond file postpone fetch 
	--   Available language bindings .... : csharp java
	-- General information:
	...

\subsection java Java

We are relying on CMake's [FindJNI.CMake](http://www.cmake.org/cmake/help/v2.8.12/cmake.html#module:FindJNI) module 
to find the JNI headers and respective libraries. On unices, it's easiest to check whether <tt>jni.h</tt> is available 
in <tt>JAVA_HOME</tt>:

	$ find $JAVA_HOME -name jni.h
	/usr/lib/jvm/java-7-openjdk-i386/include/jni.h

In addition, you will need apache's <tt>ant</tt> in the path or in <tt>$ENV{ANT_HOME}/bin</tt>:

	$ ant -version
	Apache Ant(TM) version 1.8.2 compiled on September 22 2011

If both of these are given, you ought to get <tt>java</tt> as an available language binding and a new target called
<tt>java</tt> for your build system. If you used plain Makefiles (default on unices), you will get everything you need via:

	$ make && make jar
	$ ls lib/*.jnilib lib/*.jar
	lib/libuscxmlNativeJava64.jnilib lib/uscxml.jar

The <tt>uscxml.jar</tt> is to be added to your project's classpath, while the <tt>libuscxmlNativeJava64.jnilib</tt> 
(or .so, .dll) needs to be loaded <b>once</b> via <tt>System.load()</tt> before you can use native objects.

\subsection csharp CSharp

For the CSharp bindings, we need to find either <tt>csc.exe</tt> from the Microsoft.NET framework or <tt>dmcs</tt> 
from the mono project. We search the following places for these:

	$ENV{CSC_HOME}; $ENV{DMCS_HOME}
	"C:/Windows/Microsoft.NET/Framework/v3.5"
	"C:/Windows/Microsoft.NET/Framework/v4.0.30319"

If we find one of those binaries (and SWIG obviously), we will enable the language bindings.

	$ which dmcs
	/opt/local/bin/dmcs

Again, if you used plain Makefiles, you will get everything you need via:

	$ make && make csharp
	$ find lib -type f -iname *csharp*
	lib/csharp/libuscxmlNativeCSharp.so
	lib/uscxmlCSharp.dll

The <tt>libuscxmlNativeCSharp.so</tt> has to be available to your C# runtime, either by installing it in 
<tt>/usr/local/lib</tt> or (preferred) by using <tt>LD_PRELOAD</tt> or <tt>SetDllDirectory</tt>. See the
embedding examples. The <tt>uscxmlCSharp.dll</tt> contains the managed code portion and needs to be added
to your C# project as a reference.

<b>Note:</b> You cannot use uSCXML with Xamarin Studio / Mono on Mac out of the box, as they <emph>still</emph> 
have no 64Bit support. The last Macintosh without 64Bit support was the (late 2006) Mac Mini with an Intel Core Duo.

\subsection important-windows Important Note for Windows

You cannot use CMake projects generated for Visual Studio to build the target language specific part of the
various bindings - you have to use <tt>nmake</tt> at a command prompt. Open a <tt>Visual Studio [x64 Win64] 
Command Prompt (2012)</tt> and type:

	> cd c:\path\to\build\dir
	> cmake -G"NMake Makefiles" c:\path\to\uscxml\source
	...
	> nmake && nmake csharp && nmake jar
	...

