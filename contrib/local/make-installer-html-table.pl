#!/usr/bin/perl -w

use strict;
use Cwd 'abs_path';      # abs_path
use Cwd;                 # getcwd
use File::Spec;          # abs2rel
use Data::Dumper;        # recursively dump data structures via Dumper($foo)
use File::Path;          # make_path
use File::Path qw(make_path);
use File::Temp qw/ tempfile tempdir /;
use File::Basename;

my $script_dir = dirname(abs_path($0));
my $orig_cwd = getcwd;

# get last version where we bumped the version string (ignoring pre, rc, beta ..)
my $cmake_edits = `git log --follow -p $script_dir/../../CMakeLists.txt`;
my $commit_hash;
foreach my $line (split("\n", $cmake_edits)) {
	if ($line =~ /^commit ([\dabcdef]+)/) {
		$commit_hash = $1;
	}
	last if ($commit_hash and $line =~ /\+SET\(UMUNDO_VERSION_PATCH \"\d+\"\)/);
}
my $change_log = `git log --pretty=format:"%H %h @@@ %ai: %s ### %b" $commit_hash..`;
# remove empty bodies
#$change_log =~ s/\n\n/\n/g;
# link to commit on github
$change_log =~ s/([\dabcdef]+) ([\dabcdef]+) @@@/<a href="https:\/\/github\.com\/tklab-tud\/umundo\/commit\/$1">$2<\/a>/g;
# put body below commit message
$change_log =~ s/###\s\n/\n/g;
$change_log =~ s/###\s/\n\n    /g;
$change_log =~ s/\n([^<])/\n    $1/g;


my $installer_dir = shift or die("Expected directory as first argument\n");
if (!File::Spec->file_name_is_absolute($installer_dir)) {
	$installer_dir = File::Spec->rel2abs($installer_dir, getcwd);
}

my $descriptions = {
	'./bin/protoc-umundo-cpp-rpc.*' => 'ProtoBuf RPC plugin for C++',
	'./bin/protoc-umundo-java-rpc.*' => 'ProtoBuf RPC plugin for Java',
	'./bin/umundo-monitor.*' => 'Diagnosis tool (somewhat unmaintained)',
	'./bin/umundo-pingpong.*' => 'Test deployments (i=incoming, o=outgoing)',
	'./include/umundo/core.h' => 'C++ headers for core layer',
	'./include/umundo/rpc.h' => 'C++ headers for remote procedure calls',
	'./include/umundo/s11n.h' => 'C++ headers for object serialization',
	'./include/umundo/util.h' => 'C++ headers for utilities',
	'./lib' => 'Pure C++ libraries',
	'./lib/libumundoNativeJava[\.6].*' => 'SWIG generated JNI wrapper (included in JAR)',
	'./lib/libumundocore[\.6].*' => 'C++ library for core',
	'./lib/libumundorpc[\.6].*' => 'C++ library for remote procedure calls',
	'./lib/libumundoserial[\.6].*' => 'C++ library for serialization',
	'./lib/libumundoutil[\.6].*' => 'C++ library with utilities',
	'./lib/umundo-monitor.lib' => 'not sure',
	'./lib/umundo-pingpong.lib' => 'not sure',
	'./lib/umundoNativeCSharp[\.6].*' => 'SWIG generated C# backend for DLLInvoke',
	'./share/umundo/android-8' => 'Cross compiled binaries for Android',
	'./share/umundo/android-8/armv5te/libumundoNativeJava.so' => 'SWIG generated JNI wrapper',
	'./share/umundo/android-8/umundo.jar' => 'JAR for Android (without JNI inside)',
	'./share/umundo/lib/umundo.jar' => 'JAR for desktops (auto-loading JNI code inside)',
	'./share/umundo/lib/umundoCSharp.dll' => 'C# library with managed code',
	'./share/umundo/prebuilt' => 'Prebuilt libraries in case we forgot something',
	'./share/umundo/samples' => 'Sample programs and IDE templates',
	'./share/umundo/samples/android' => 'Sample programs for Android',
	'./share/umundo/samples/android/umundo-pingpong/libs' => 'These are just placehoders!',
	'./share/umundo/samples/android/umundo-pingpong/libs/armeabi/libumundoNativeJava.so' => 'Replace with real library from above!',
	'./share/umundo/samples/android/umundo-pingpong/libs/armeabi/libumundoNativeJava_d.so' => 'Replace with real library from above!',
	'./share/umundo/samples/android/umundo-pingpong/libs/umundo.jar' => 'Replace with real library from above!',
	'./share/umundo/samples/csharp' => 'Sample programs for C#',
	'./share/umundo/samples/csharp/umundo-pingpong' => 'The simplest umundo program in C#',
	'./share/umundo/samples/csharp/umundo-s11ndemo' => 'Serialization in C# (Dirk is working on it)',
	'./share/umundo/samples/csharp/umundo.s11n' => 'My initial attempts at serialization with C# (deprecated)',
	'./share/umundo/samples/ios' => 'Sample programs for iOS',
	'./share/umundo/samples/ios/umundo-pingpong' => 'The simplest umundo program for iOS',
	'./share/umundo/samples/java' => 'Sample programs for Java',
	'./share/umundo/samples/java/core/chat' => 'Chat using the core layer',
	'./share/umundo/samples/java/core/chat/build.properties' => 'Adapt these for your system',
	'./share/umundo/samples/java/rpc/chat' => 'Chat using the RPC layer',
	'./share/umundo/samples/java/rpc/chat/build.properties' => 'Adapt these for your system',
	'./share/umundo/samples/java/rpc/chat/proto/ChatS11N.proto' => 'ProtoBuf file for chat services',
	'./share/umundo/samples/java/s11n/chat' => 'Chat using the serialization layer',
	'./share/umundo/samples/java/s11n/chat/build.properties' => 'Adapt these for your system',
	'./share/umundo/samples/java/s11n/chat/proto/ChatS11N.proto' => 'ProtoBuf file for chat message objects',
	'./share/umundo/samples/cpp' => 'Sample programs for C++',
	'./share/umundo/samples/cpp/core/chat' => 'Chat using the core layer',
	'./share/umundo/samples/cpp/rpc/chat' => 'Chat using the RPC layer',
	'./share/umundo/samples/cpp/s11n/chat' => 'Chat using the serialization layer',
	'./share/umundo/samples/cpp/s11n/chat/proto/ChatS11N.proto' => 'ProtoBuf file for chat message objects',
	'./share/umundo/samples/cpp/rpc/chat/proto/ChatS11N.proto' => 'ProtoBuf file for chat services',
	'./share/umundo/cmake/FindUMundo.cmake' => 'CMake module to find umundo once it is installed',
	'./share/umundo/cmake/UseUMundo.cmake' => 'CMake macros for protobuf',
};

my ($mac_archive, $linux32_archive, $linux64_archive, $win32_archive, $win64_archive);
my ($mac_files, $linux32_files, $linux64_files, $win32_files, $win64_files);

chdir $installer_dir;
foreach (sort <*>) {
	next if m/^\./;
	$mac_archive         = File::Spec->rel2abs($_, getcwd) if (m/.*darwin.*\.tar\.gz/i);
	$linux32_archive     = File::Spec->rel2abs($_, getcwd) if (m/.*linux-i686.*\.tar\.gz/i);
	$linux64_archive     = File::Spec->rel2abs($_, getcwd) if (m/.*linux-x86_64.*\.tar\.gz/i);
	$win32_archive       = File::Spec->rel2abs($_, getcwd) if (m/.*windows-x86-.*\.zip/i);
	$win64_archive       = File::Spec->rel2abs($_, getcwd) if (m/.*windows-x86_64.*\.zip/i);
}

print STDERR "No archive for MacOSX found!\n" if (!$mac_archive);
print STDERR "No archive for Linux 32Bit found!\n" if (!$linux32_archive);
print STDERR "No archive for Linux 64Bit found!\n" if (!$linux64_archive);
print STDERR "No archive for Windows 32Bit found!\n" if (!$win32_archive);
print STDERR "No archive for Windows 64Bit found!\n" if (!$win64_archive);

$mac_archive =~ m/.*darwin-i386-(.*)\.tar\.gz/;
my $version = $1;

#                    make a hash     remove first element      split into array at newline
%{$mac_files}      = map { $_ => 1 } map { s/^[^\/]*\///; $_ } split("\n", `tar tzf $mac_archive`)      if $mac_archive;
%{$linux32_files}  = map { $_ => 1 } map { s/^[^\/]*\///; $_ } split("\n", `tar tzf $linux32_archive`)  if $linux32_archive;
%{$linux64_files}  = map { $_ => 1 } map { s/^[^\/]*\///; $_ } split("\n", `tar tzf $linux64_archive`)  if $linux64_archive;
%{$win32_files}    = map { $_ => 1 } map { s/^[^\/]*\///; $_ } split("\n", `unzip -l $win32_archive`)   if $win32_archive;
%{$win64_files}    = map { $_ => 1 } map { s/^[^\/]*\///; $_ } split("\n", `unzip -l $win64_archive`)   if $win64_archive;

# print Dumper($mac_files);
# exit;
my $tmpdir = File::Temp->newdir() or die($!);
#print STDERR $tmpdir."\n";
chdir $tmpdir or die($!);

system("tar", "xzf", $mac_archive)      if $mac_archive;
system("tar", "xzf", $linux32_archive)  if $linux32_archive;
system("tar", "xzf", $linux64_archive)  if $linux64_archive;
system("unzip", "-q", $win32_archive)         if $win32_archive;
system("unzip", "-q", $win64_archive)         if $win64_archive;

my $rv;
mkdir("content") or die($!);
foreach (sort <*>) {
	next if m/^\./;
	next if m/.*content/;
	if ($_ !~ /.*windows.*/i) {
		$rv = `ditto $_/usr/local content`;
	} else {
		$rv = `ditto $_ content`;		
	}
	$rv = `rm -rf $_`;
}

# remove duplicates and uninteresting directories
# $rv = `rm -rf content/bin/protoc-umundo-cpp-rpc.exe`;
# $rv = `rm -rf content/bin/protoc-umundo-java-rpc.exe`;
# $rv = `rm -rf content/bin/umundo-monitor.exe`;
# $rv = `rm -rf content/bin/umundo-pingpong.exe`;

$rv = `rm -rf content/include/umundo/common`;
$rv = `rm -rf content/include/umundo/connection`;
$rv = `rm -rf content/include/umundo/discovery`;
$rv = `rm -rf content/include/umundo/protobuf`;
$rv = `rm -rf content/include/umundo/rpc`;
$rv = `rm -rf content/include/umundo/s11n`;
$rv = `rm -rf content/include/umundo/thread`;
$rv = `rm -rf content/include/umundo/util`;
$rv = `rm -rf content/include/umundo-objc`;

chdir "content/" or die($!);

my $tree_list = `tree -a -h --noreport --charset ISO-8859-1`;
my $flat_list = `find -s .`;

print '<html><body>'."\n";

print '<h1>Changelog</h1>'."\n";
print '<pre>'."\n";
print $change_log;
print '</pre>'."\n";

print '<h1>Contents</h1>';
print <<EOF;
<p>The following table is an excerpt of all the files in the individual installer 
packages (detailled C++ headers are not shown). All the different archives/installers 
for a given platform contain the same files, it is only a matter of taste and 
convenience. There are differences between the contents for each platform though 
and they are listed in the <i>availability</i> column.</p>

<p><tt>Mac</tt> are all the darwin installers, <tt>L32</tt> and <tt>L64</tt> is short for Linux 32 and 64Bit
respectively, same with <tt>W32</tt> and <tt>W64</tt> for Windows. Only the first occurence of a 
library is commented, the <tt>_d</tt> suffix signifies debug libraries, the <tt>64</tt> 
suffix is for 64Bit builds and the Windows libraries have no <tt>lib</tt> prefix.</p>

EOF
print '<table>'."\n";
print '<tr><th align="left">Availability</th><th align="left">Filename</th><th align="left">Description</th></tr>';
print '<tr><td valign="top">'."\n";
print '<pre>'."\n";

foreach my $file (split("\n", $flat_list)) {
	if ($file eq '.') {
		print '<font bgcolor="#ccc">MAC</font>|L32|L64|W32|W64'."\n";
		next;
	}
	if (-d $file) {
		print "\n";
		next;
	}
	$file =~ s/\.\///;
#	print STDERR $file."\n";
	(exists($mac_files->{"usr/local/$file"}) ? print " X  " : print " -  ");
	(exists($linux32_files->{"usr/local/$file"}) ? print " X  " : print " -  ");
	(exists($linux64_files->{"usr/local/$file"}) ? print " X  " : print " -  ");
	(exists($win32_files->{"$file"}) ? print " X  " : print " -  ");
	(exists($win64_files->{"$file"}) ? print " X  " : print " -  ");
	print "\n";
}

print '</pre>'."\n";
print '</td><td valign="top">'."\n";
print '<pre>'."\n";

print $tree_list;

print '</pre>'."\n";
print '</td><td valign="top">'."\n";
print '<pre>'."\n";

foreach my $file (split("\n", $flat_list)) {
	my $has_description = 0;
	foreach my $desc (keys %{$descriptions}) {
		if ($file =~ /^$desc$/) {
			print $descriptions->{$desc}."\n";
			delete $descriptions->{$desc};
			$has_description = 1;
		}
	}
	if (!$has_description) {
		print "\n";
	}
}

print '</pre>'."\n";
print '</td></tr>'."\n";
print '</table>'."\n";
print '</body></html>'."\n";

chdir $orig_cwd;