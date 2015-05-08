# Building from Source

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**

- [General](#general)
- [Build Dependencies](#build-dependencies)
- [Platform Notes](#platform-notes)
    - [Mac OSX](#mac-osx)
    - [Linux](#linux)
    - [Windows](#windows)
    - [iOS](#ios)
    - [Raspberry Pi](#raspberry-pi)
- [Language Bindings](#language-bindings)
    - [Java](#java)
    - [CSharp](#csharp)
    - [Important Note for Windows](#important-note-for-windows)
- [Optional Functionality](#optional-functionality)
- [About 32/64Bit Support](#about-3264bit-support)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## General

The source code is built using CMake, the process of building uscxml is
essentially the same on every platform:

1. Read the <b>[Platform Notes](#platforn-notes)</b> below to prepare your system.
2. Checkout uscxml into a convenient directory:

	<tt>git clone git://github.com/tklab-tud/uscxml.git</tt>

3. Create a new directory for an *out-of-source* build. I usually create sub-directories
in <tt>&lt;USCXML_SRC&gt;/build/</tt>.
4. Run cmake (or ccmake / CMake-GUI) to create the files required by your actual build-system.
5. Use your actual build-system or development environment to build uscxml.
6. Optionally build the [language bindings](#language-bindings) to embed the SCXML interpreter in another language.
7. Read the SCXML draft and have a look at the tests to get started.

If you want to build for another IDE or build-system, just create a new
*out-of-source* build directory and start over with CMake. To get an idea of
supported IDEs and build-environments on your platform, type <tt>cmake --help</tt>
or run the CMake-GUI and look for the *Generators* section at the end of the
output. Default on Unices is Makefiles.

<b>Note:</b> If you plan to use Eclipse CDT, you cannot have a build directory anywhere under 
the source directory - just create the build directory anywhere else. This only applies to the Eclipse CDT
project generator.

<b>Note:</b> You cannot build the language bindings with the Visual Studio project as it croaks when calling SWIG,
just have another build directory with the "NMake Makefiles" project generator.

## Build Dependencies

Overview of the uscxml dependencies. See the [Platform Notes](#platform-notes) for details.

<b>Note:</b> We download pre-compiled versions of most dependencies at CMake configure-time. If you want
to provide you own libraries, remove them from <tt>&lt;USCXML_SRC&gt;/contrib/prebuilt/</tt> and provide
your own.

<table>
    <tr><th>Platform</th><th>Dependency</th><th>Version</th><th>Comment</th></tr>
	<tr>
		<td rowspan="10"><b>Everyone</b></td>
			<td><a href="http://www.cmake.org/cmake/resources/software.html">CMake</a><br />required</td>
			<td>>=&nbsp;2.8.6</td>
			<td>The build-system used for uscxml.</td></tr>
		<tr>
			<td><a href="http://www.swig.org">SWIG</a><br />optional</td>
			<td>>=&nbsp;2.0.6</td>
			<td>Generates language bindings to embed uSCXML in other target languages.</td></tr>
		<tr>
			<td><a href="http://libevent.org">libevent</a><br />pre-compiled</td>
			<td>>=&nbsp;2.1.x</td>
			<td>Event queues with callbacks and the HTTP server.</td></tr>
		<tr>
			<td><a href="http://curl.haxx.se">curl</a><br />pre-compiled / required</td>
			<td>>=&nbsp;7.29.0</td>
			<td>URL downloads.</td></tr>
		<tr>
			<td><a href="http://code.google.com/p/v8/">v8</a><br />pre-compiled</td>
			<td>svn checkout</td>
			<td>ECMAScript datamodel implementation.</td></tr>
		<tr>
			<td><a href="http://www.swi-prolog.org">SWI Prolog</a><br />pre-compiled for unices</td>
			<td>>=&nbsp;6.3.x</td>
			<td>Prolog datamodel implementation.</td></tr>
		<tr>
			<td><a href="http://code.google.com/p/google-glog/">glog</a><br />pre-compiled</td>
			<td>>=&nbsp;0.3.3</td>
			<td>Logging library.</td></tr>
		<tr>
			<td><a href="https://github.com/jezhiggins/arabica">Arabica</a><br />pre-compiled</td>
			<td>>=&nbsp;git checkout</td>
			<td>XML DOM / XPath / XML Events.</td></tr>
		<tr>
			<td><a href="http://www.sqlite.org">SQLite</a><br />optional</td>
			<td>>=&nbsp;3.7.15.2</td>
			<td>Persistence and sqlite invoker.</td></tr>
		<tr>
			<td><a href="http://www.openscenegraph.com">OpenSceneGraph</a><br />optional</td>
			<td>>=&nbsp;3.1.X</td>
			<td>3D invokers (scenegraph, osgconvert).</td></tr>
		<tr>
			<td><a href="http://www.stack.nl/~dimitri/doxygen/">Doxygen</a><br />recommended</td>
			<td></td>
			<td>Used by <tt>make docs</tt> to generate documentation from source comments.</td></tr>
	</tr>
	<tr bgcolor="grey"><td bgcolor="#dddddd" colspan="4"></td></tr>

	<tr>
		<td rowspan="3"><b>Mac OSX</b></td>
			<td><a href="http://developer.apple.com/xcode/">XCode</a><br />required</td>
			<td>4.2.1 works</td>
			<td>Apples SDK with all the toolchains.</td></tr>
		<tr>
			<td><a href="http://www.macports.org/">MacPorts</a><br />recommended</td>
			<td>>= 2.0.3</td>
			<td>Build system for a wide selection of open-source packages.</td></tr>
		<tr>
			<td><a href="http://www.xmlsoft.org">libxml2</a><br />pre-installed</td>
			<td>>= 2.6.16</td>
			<td>Actual XML parser used by Arabica.</td></tr>
	</tr>

	<tr>
		<td rowspan="1"><b>Linux</b></td>
			<td><a href="http://www.xmlsoft.org">libxml2</a><br />required</td>
			<td>>= 2.6.16</td>
			<td>Actual XML parser used by Arabica.</td></tr>
	</tr>

	<tr>
	<td rowspan="1"><b>Windows</b></td>
		<td<a href="http://www.microsoft.com/visualstudio/en-us">Visual&nbsp;Studio&nbsp;10</a><br />required</td>
		<td>v10 pro works</td>
		<td>As a student, you can get your version through MSAA.</td></tr>
	</tr>
</table>

## Platform Notes

The following sections will detail the preparation of the respective platforms to ultimately compile uscxml.

## Mac OSX

You will have to install <tt>CMake</tt> via Macports:

	# required dependencies
	$ sudo port install cmake
	
	# optional dependencies for language bindings
	$ sudo port install apache-ant swig-java swig-php swig-csharp

	# other optional dependencies
	$ sudo port install lua swi-prolog-devel ffmpeg-devel libical expect libpurple OpenSceneGraph-devel protobuf-cpp 

The rest is pre-installed or downloaded at configure-time as pre-compiled libraries.
Just download the source and invoke CMake to create Makefiles or a Xcode project.

### Console / Make

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the uscxml-browser with a test.scxml file:

	$ ./bin/uscxml-browser ../../test/uscxml/test-ecmascript.scxml

### Xcode

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/xcode && cd build/xcode
	$ cmake -G Xcode ../..
	[...]
	-- Build files have been written to: .../build/xcode
	$ open uscxml.xcodeproj

You can of course reuse the same source directory for many build directories.

## Linux

Depending on your distribution, you will most likely have apt-get or yum available as package managers.
If you do not, I'll have to assume that you are knowledgable enough to resolve build dependencies on your own.

### Preparing *apt-get based* distributions

This would be all distributions based on Debian, like Ubuntu, Linux Mint and the like.

	# build system and compiler
	$ sudo apt-get install git cmake cmake-curses-gui make g++

	# uscxml required dependencies
	$ sudo apt-get install libxml2-dev libcurl4-openssl-dev

There may still be packages missing due to the set of dependencies among packages
in the various distributons. Try to run CMake and resolve dependencies until you
are satisfied.

### Preparing *yum based* distributions

This would be all distributions based on Redhat, e.g. Fedora.

	# build system and compiler
	$ sudo yum install git cmake cmake-gui gcc-c++

	# uscxml required dependencies
	$ sudo yum install xml2-devel libcurl-devel

### Fedora 20

Here is a complete walk-through to get uscxml running on Fedora 20, starting with the net installer.

	# get us git and the developer tools
	$ sudo yum install git gcc-c++ cmake
	
	# uscxml required dependencies
	$ sudo yum install libxml2-devel libcurl-devel

This is sufficient to get uscxml to build. If you want some more functionality, install some more libraries:

	# SWI prolog datamodel
	$ sudo yum install pl-devel

	# OpenAL invoker
	$ sudo yum install openal-soft-devel libsndfile-devel

	# scenegraph and osgconvert invoker
	$ sudo yum install OpenSceneGraph-devel mesa-libGL-devel
	
	# ffmpeg invoker (add repository from http://rpmfusion.org)
	$ sudo yum install ffmpeg-devel ffmpeg-compat-devel

	# calendar invoker
	$ sudo yum install libical-devel

	# expect invoker
	$ sudo yum install expect-devel tk-devel

	# instant messaging invoker
	$ sudo yum install libpurple-devel

### Console / Make

Instructions are a literal copy of building uscxml for MacOSX on the console from above:

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the uscxml-browser with a test.scxml file:

	$ ./bin/uscxml-browser ../../test/uscxml/test-ecmascript.scxml

### Eclipse CDT

<b>Note:</b> Eclipse does not like the project to be a subdirectory in the source.
You have to choose your build directory with the generated project accordingly.

	$ mkdir -p ~/Desktop/build/uscxml/eclipse && cd ~/Desktop/build/uscxml/eclipse
	$ cmake -G "Eclipse CDT4 - Unix Makefiles" <USCXML_SRCDIR>
	[...]
	-- Build files have been written to: .../build/uscxml/eclipse

Now open Eclipse CDT and import the out-of-source directory as an existing project into workspace, leaving the "Copy projects
into workspace" checkbox unchecked. There are some more [detailed instruction](http://www.cmake.org/Wiki/Eclipse_CDT4_Generator) available
in the CMake wiki as well.

## Windows

Building from source on windows is somewhat more involved and instructions are necessarily in prose form. These 
instructions were created using Windows 7 and MS Visual Studio 2010.

### Prepare compilation

1. Use git to **checkout** the source from <tt>git://github.com/tklab-tud/uscxml.git</tt>
	into any convenient directory. 

2. Start the **CMake-GUI** and enter the checkout directory in the "Where is the source
	code" text field. Choose any convenient directory to build the binaries in.

3. Hit "**Configure**" and choose your toolchain and compiler - I only tested with
	Visual Studio 10. Hit "Configure" again until there are no more red items in
	the list. If these instructions are still correct and you did as described
	above, you should be able to "Generate" the Visual Project Solution.

Now you can generate the MS Visual Studio project file <tt><USCXML_BUILDIR>/uscxml.sln</tt>.
Just open it up to continue in your IDE.

<b>Note:</b> We only tested with the MSVC compiler. You can try to compile
with MinGW but you would have to build all the dependent libraries as well.

<b>Note:</b> We do no provide prebuilt dependencies for MSVC18.x (Visual Studio 2012 / 2013). 
You can still use the bindings for C#, but not the native C++ libraries.

## iOS

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

## Raspberry Pi

To compile uSCXML on Raspberry Pi you will need to, at a minimum, install the following packages. This assumes that
you run Raspberry, the Debian variant.

	$ sudo apt-get install cmake libxml2-dev libcurl4-gnutls-dev

Now you can compile uSCXML like on any other platform:

	$ git clone --depth 1 https://github.com/tklab-tud/uscxml.git
	$ mkdir -p uscxml/build/raspberry && cd uscxml/build/raspberry
	$ cmake ../..
	$ make

If you want an ECMAScript datamodel or LUA, you will need to install additional packages:

	# additional datamodels: ECMAScript, LUA, Prolog
	$ sudo apt-get install libjavascriptcoregtk-3.0-dev liblua5.2-dev swi-prolog-nox

	# additional invokers
	$ sudo apt-get install libical-dev libpurple-dev libopenal-dev libsndfile1-dev libopenscenegraph-dev

Lastly, to get the language bindings install SWIG and the developer kits of the respective language. Older Java
versions will work as well (>= 1.5), just make sure <tt>JAVA_HOME</tt> is set correctly.

	# language bindings: Java, CSharp
	$ sudo apt-get install swig ant oracle-java8-jdk mono-mcs
	$ echo $JAVA_HOME
	/usr/lib/jvm/jdk-8-oracle-arm-vfp-hflt

<b>Note:</b> The version of the V8 JavaScript engine in Raspbian is not compatible with uSCXML.

## Language Bindings

In order to build any language bindings, you will need to have SWIG and the development kit of your target language
installed. The set of available language bindings is printed at the end of the CMake invocation:

	$ cmake <USCXML_SRC>
	...
	--   Available custom elements ...... : respond file postpone fetch 
	--   Available language bindings .... : csharp java
	-- General information:
	...

### Java

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

	$ make && make java
	$ ls lib/*.jnilib lib/*.jar
	lib/libuscxmlNativeJava64.jnilib lib/uscxml.jar

The <tt>uscxml.jar</tt> is to be added to your project's classpath, while the <tt>libuscxmlNativeJava64.jnilib</tt> 
(or .so, .dll) needs to be loaded <b>once</b> via <tt>System.load()</tt> before you can use native objects.

### CSharp

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

### Important Note for Windows

You cannot use CMake projects generated for Visual Studio to build the target language specific part of the
various bindings - you have to use <tt>nmake</tt> at a command prompt. Open a <tt>Visual Studio [x64 Win64] 
Command Prompt (2010)</tt> and type:

	> cd c:\path\to\build\dir
	> cmake -G"NMake Makefiles" c:\path\to\uscxml\source
	...
	> nmake && nmake csharp && nmake java
	...

## Optional Functionality

At configure time, CMake will search for various libraries and conditionally compile only the part of uSCXML for
which libraries have been found. On unices, it is straight forward to add libraries and - if you installed them to
their default location - CMake will usually pick them up. On Windows, however, the process is more complicated.
While we try to search in the locations where the various installers saved the header files and libraries, there are
some of distributed only as an archive.

If you want to give CMake the best chance of picking up these libraries, put them into the <emph>platform prebuilt path</emph>.
This path is located in <tt>&lt;USCXML_SRC>/contrib/prebuilt/&lt;PLATFORM>/&lt;COMPILER></tt>. For Windows 32bit, 
with MSVC this path is <tt>&lt;USCXML_SRC>/contrib/prebuilt/windows-x86/msvc</tt>.

For instance, in order to enable the <tt>lua</tt> datamodel on windows, download the static lua libraries and save 
the dll in <tt>&lt;PREBUILT>/lib/lua52.lib</tt> and the header files directly in <tt>&lt;PREBUILT>/include/</tt>. 
When you run CMake for the first time, it will automatically create these paths for you.

<b>Note:</b> Actually, we would have to differentiate the various MSVC versions as well: v16 (VS2010) and v18 (VS2012/13)
employ a different application binary interface (ABI). This is approach is taken e.g. in uMundo with <tt>msvc16</tt> 
vs <tt>msvc18</tt>, but not yet realized for uSCXML.

## About 32/64Bit Support

We do support both, 32 and 64Bit for Linux and Windows. On Macintosh, most prebuilt dependencies are compiled as 
universal binaries with 32/64Bit but we build 64Bit binaries exclusively. The reason is that e.g. <tt>curl</tt>
cannot be compiled as a universal binary as its header files make assumptions about the size of an int.
Furthermore, most libraries used by invokers are provided by brew or Macports will be 64Bit only and fail to link.

If you feel adventurous, you can uncomment <tt>set(CMAKE_OSX_ARCHITECTURES "i386;x86_64")</tt> in the topmost
<tt>CMakeLists.txt</tt> and fight your way through the linker errors.
 