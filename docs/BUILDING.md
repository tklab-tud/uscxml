# Building from Source

The source code is built using CMake, the process of building uscxml is
essentially the same on every platform:

1. Read the <b>[Platform Notes](#platform-notes)</b> below to prepare your system.
2. Checkout uscxml into a convenient directory:

	<tt>git clone git://github.com/tklab-tud/uscxml.git</tt>

3. Create a new directory for an *out-of-source* build. I usually create sub-directories
in <tt>&lt;USCXML_SRC&gt;/build/</tt>.
4. Run cmake (or ccmake / CMake-GUI) to create the files required by your actual build-system.
5. Use your actual build-system or development environment to build uscxml.
6. Read the SCXML draft and have a look at the tests to get started.

If you want to build for another IDE or build-system, just create a new
*out-of-source* build directory and start over with cmake. To get an idea of
supported IDEs and build-environments on your platform, type <tt>cmake --help</tt>
or run the CMake-GUI and look for the *Generators* section at the end of the
output. Default on Unices is Makefiles.

# Build Dependencies

Overview of the uscxml dependencies. See the [Platform Notes](#platform-notes) for details.

<b>Note:</b> We download pre-compiled versions of most dependencies at cmake configure-time. If you want
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
			<td><a href="http://libevent.org">libevent</a><br />pre-compiled</td>
			<td>>=&nbsp;2.1.x</td>
			<td>Event queues with callbacks and the HTTP server.</td></tr>
		<tr>
			<td><a href="http://curl.haxx.se">curl</a><br />pre-compiled</td>
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
		<td bgcolor="#ffffdd"><a href="http://www.microsoft.com/visualstudio/en-us">Visual&nbsp;Studio&nbsp;10</a><br />required</td>
		<td>v10 pro works</td>
		<td>As a student, you can get your version through MSAA.</td></tr>
	</tr>
</table>

# Platform Notes

This section will detail the preparation of the respective platforms to ultimately compile uscxml.

## Mac OSX

You will have to install <tt>cmake</tt> via Macports:

	sudo port install cmake

The rest is pre-installed or downloaded at configure-time as pre-compiled libraries.
Just download the source and invoke CMake to create Makefiles or a Xcode project.

### Console / Make

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the mmi-browser with a test.scxml file:

	$ ./bin/mmi-browser ../../test/samples/uscxml/test-ecmascript.scxml

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
	$ sudo apt-get install libxml2-dev

There may still be packages missing due to the set of dependencies among packages
in the various distributons. Try to run cmake and resolve dependencies until you
are satisfied.

### Preparing *yum based* distributions

This would be all distributions based on Redhat, e.g. Fedora.

	# build system and compiler
	$ sudo yum install git cmake cmake-gui gcc-c++

	# uscxml required dependencies
	$ sudo yum install xml2-devel

### Console / Make

Instructions are a literal copy of building uscxml for MacOSX on the console from above:

	$ cd <USCXML_SRCDIR>
	$ mkdir -p build/cli && cd build/cli
	$ cmake ../..
	[...]
	-- Build files have been written to: .../build/cli
	$ make

You can test whether everything works by starting the mmi-browser with a test.scxml file:

	$ ./bin/mmi-browser ../../test/samples/uscxml/test-ecmascript.scxml

### Eclipse CDT

<b>Note:</b> Eclipse does not like the project to be a subdirectory in the source.
You have to choose your build directory with the generated project accordingly.

	$ mkdir -p build/uscxml/eclipse && cd build/uscxml/eclipse
	$ cmake -G "Eclipse CDT4 - Unix Makefiles" <USCXML_SRCDIR>
	[...]
	-- Build files have been written to: .../build/uscxml/eclipse

Now open Eclipse CDT and import the out-of-source directory as an existing project into workspace, leaving the "Copy projects
into workspace" checkbox unchecked. There are some more [detailed instruction](http://www.cmake.org/Wiki/Eclipse_CDT4_Generator) available
in the cmake wiki as well.

### Compiling Dependencies

If the packages in your distribution are too old, you will have to compile current
binaries. This applies especially for SWI and CMake as they *need* to be rather
current. Have a look at the build dependencies above for minimum versions.

## Windows

Building from source on windows is somewhat more involved and instructions are necessarily in prose form. These instructions were
created using Windows 7 and MS Visual Studio 2010.

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

