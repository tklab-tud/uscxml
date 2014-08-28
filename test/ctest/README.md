# Setting up CTest Slaves

If you want to contribute a test-slave, just create a file called
<tt>hosts/&lt;HOSTNAME>.ctest</tt> - have a look at the existing host files.
Then setup your crontab as follows:

    50       */4   *   *   *       CTEST_SUBMIT_TYPE="Experimental"	/home/autobuilder/uscxml/test/ctest/run-tests.cron
    0        2     *   *   *       CTEST_SUBMIT_TYPE="Nightly"      /home/autobuilder/uscxml/test/ctest/run-tests.cron
    */2      *     *   *   *       CTEST_SUBMIT_TYPE="Continuous"   /home/autobuilder/uscxml/test/ctest/run-tests.cron

<b>Note:</b> Be aware that <tt>run-tests.cron</tt> is under version control and
might get updated from git with potentially surprising content. Copy the whole
ctest directory someplace safe if you are concerned and make sure to specify
<tt>USCXML_SOURCE_DIR=/uscxml/checkout/here</tt> in the crontab line.

<b>Note:</b> We will build in <tt>/tmp</tt>, make sure there is enough room for all three
build directories.

<b>Warning:</b> <tt>run-tests.cron</tt> will pull the current GIT head. Use a
dedicated source checkout for testing if this is a problem.

# How it works

<tt>run-tests.cron</tt> will setup the environment to call your host-specific
test file with <tt>ctest</tt>. If you do not provide a value for
<tt>USCXML_SOURCE_DIR</tt> it will assume that you want to work with the source
containing the script itself.

When your host-specific test file is called, you can assume the following facts:

* You are the only running ctest instance invoked by <tt>run-tests.cron</tt>
* There is a path to the ctest executable in <tt>$ENV{CTEST}</tt>
* The current working directory is the ctest directory.
* The chosen submit type is available as <tt>$ENV{CTEST_SUBMIT_TYPE}</tt>
* The path to the umundo sources is available as <tt>$ENV{UMUNDO_SOURCE_DIR}</tt>

As a host-specific test file, you are expected to prepare test-builds by setting
the following variables and call <tt>include("common.ctest.inc")</tt> for every
build you prepared.

<table>
	<tr><th>Variable</th><th>Comment</th></tr>
	<tr>
		<td><tt>CTEST_SITE</tt></td>
		<td>The name of this build-slave for reporting in the dashboard. Should be the same for all submitted test-builds</td>
	</tr>
	<tr>
		<td><tt>CTEST_CMAKE_GENERATOR</tt></td>
		<td>The generator to use with cmake (e.g. "Unix Makefiles")</td>
	</tr>
	<tr>
		<td><tt>CTEST_BUILD_CONFIGURATION</tt></td>
		<td>"Debug", "Release" ..</td>
	</tr>
	<tr>
		<td><tt>CTEST_TOOLCHAIN</tt></td>
		<td>Path to a cmake toolchain file for cross compiling.</td>
	</tr>
	<tr>
		<td><tt>CTEST_BUILD_NAME</tt></td>
		<td>Name of the particular build you are about to submit (e.g. "darwin-x86_64 llvm bonjour").</td>
	</tr>
	<tr>
		<td><tt>CTEST_BUILD_OPTIONS</tt></td>
		<td>Parameters to be passed to cmake when preparing the build. These will
			most likely come from one of the tests/*.ctest files.</td>
	</tr>
</table>

## Example from the centos6x64-vii build-slave:

    set(CTEST_CMAKE_GENERATOR "Unix Makefiles")
    set(CTEST_SITE "centos6x64-vii")
    set(CTEST_BUILD_CONFIGURATION "Debug")

    # test with avahi
    include("tests/avahi.ctest")
    set(CTEST_BUILD_NAME "linux-x86_64 gcc avahi")
    include("common.ctest.inc")

    # test for embedded bonjour
    include("tests/bonjourEmbedded.ctest")
    set(CTEST_BUILD_NAME "linux-x86_64 gcc bonjour embedded")
    include("common.ctest.inc")

    # test android cross-compile with embedded bonjour
    include("tests/bonjourEmbedded.ctest")
    set(CTEST_BUILD_NAME "linux-x86_64-android gcc bonjour embedded")
    set(CTEST_TOOLCHAIN "$ENV{UMUNDO_SOURCE_DIR}/contrib/cmake/CrossCompile-Android.cmake")
    include("common.ctest.inc")

