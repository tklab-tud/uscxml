# uSCXML ReadMe

uSCXML is a SCXML interpreter written in C/C++. It is mostly feature-complete and
[standards compliant](https://github.com/tklab-tud/uscxml#test-reports) to a large extend.
It runs on <b>Linux</b>, <b>Windows</b> and <b>MacOSX</b>, each 32- as well as 64Bits.
There are still a few rough edges, especially with the plugins and custom extensions.

There is no technical reason for it not to run on iOS and Android as well, but we did not yet setup
the respective build-process and did not precompile required libraries.

   * <b>Datamodels</b>
       * Full ECMAScript datamodel using Google's v8 and JavaScriptCore (JSC is incomplete)
       * Full NULL datamodel with required <tt>In</tt> predicate
       * Early Prolog datamodel using SWI prolog
       * Rudimentary support for XPath datamodel (W3C tests not yet implementable)
   * <b>Invokers</b>
       * <tt>scxml</tt>: Invoke a nested scxml interpreter
       * <tt>dirmon</tt>: Watches a directory for changes to files
       * <tt>scenegraph</tt>: Simplified 3D scenegraphs with custom markup
       * <tt>heartbeat</tt>: Periodically sends events
       * <tt>umundo</tt>: Subscribe to channels and publish events
   * <b>DOM</b>
       * DOM Core Level 2 + XPath extensions available for ecmascript datamodel
       * Namespace aware to embed custom markup for special invokers
   * <b>Communication</b>
       * Features the standard basichttp io-processor
       * Features the required SCXML io-processor
       * <b>No</b> DOM io-processor
       * Can actually respond to HTTP requests with data via &lt;response>
   * <b>Language Bindings</b>
       * PHP module for apache and cli interpreter

## Test Reports

 * We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. 
 * Have a look at the [result](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml) for the various platforms.
 * The manual tests are [excluded](https://github.com/tklab-tud/uscxml/blob/master/contrib/ctest/CTestCustom.ctest.in).

uSCXML still fails the following ecmascript tests:

<table>
	<tr><th>Test#</th><th>Status</th><th>Description</th><th>Comment</th></tr>
	<tr>
		<td><tt><a href="https://github.com/tklab-tud/uscxml/blob/master/test/samples/w3c/ecma/test301.scxml">301</a></tt></td>
		<td><tt>Failed</tt></td>
		<td>"the processor should  reject this document because it can't download the script"</td>
		<td>uSCXML continues processing as if there was no <tt>&lt;script></tt> element.</td>
	</tr>
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
</table>

## License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

## Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md).
