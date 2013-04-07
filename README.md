# uSCXML ReadMe

uSCXML is a SCXML interpreter written in C/C++. It is [mostly feature-complete](https://github.com/tklab-tud/uscxml#test-reports) 
as far as the W3C SCXML draft specifies. It runs on <b>Linux</b>, <b>Windows</b> and <b>MacOSX</b>, each 32- as well as 64Bits. 

There is no technical reason for it not to run on iOS and Android as well, but we did not yet setup
the respective build-process.

   * <b>Datamodels</b>
       * ECMAScript using Google's v8 and JavaScriptCore (JSC is incomplete)
       * Prolog using SWI prolog
       * No NULL datamodel yet
       * No XPath datamodel yet
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
       * No DOM io-processor
       * Can actually respond to HTTP requests with data via &lt;response>
   * <b>Language Bindings</b>
       * PHP module for apache and cli interpreter

## Test Reports

We continuously run the [W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML. The results the for
various platforms can be [found here](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml).
There are a few [excluded tests](https://github.com/tklab-tud/uscxml/blob/master/contrib/ctest/CTestCustom.ctest.in) 
regarding the <tt>NULL</tt> and <tt>XPath</tt> datamodel, as well as the manual tests.

uSCXML still fails the following tests:

<table>
	<tr><th>Test#</th><th>Status</th><th>Description</th><th>Comment</th></tr>
	<tr>
		<td><tt>301</tt></td>
		<td><tt>Failed</tt></td>
		<td>"the processor should  reject this document because it can't download the script"</td>
		<td>uSCXML continues processing as if there was no <tt>&lt;script></tt> element.</td>
	</tr>
	<tr>
		<td><tt>329</tt></td>
		<td><tt>Failed</tt></td>
		<td>"test that none of the system variables can be modified"</td>
		<td>uSCXML allows writing to <tt>_event</tt>. This is very useful to have a scope 
			that vanishes when processing an event is finished.</td>
	</tr>
	<tr>
		<td><tt>346</tt></td>
		<td><tt>Failed</tt></td>
		<td>"test that any attempt to change the value of a system variable causes error.execution to be raised"</td>
		<td>Same issue as above: we allow writing to <tt>_event</tt>.</td>
	</tr>
	<tr>
		<td><tt>488</tt></td>
		<td><tt>Failed</tt></td>
		<td>"test that illegal expr in <param> produces error.execution and empty event.data"</td>
		<td>The actual meaning of <emph>empty</emph> is still ambiguous - in test 343 it is assumed to be <tt>undefined</tt>.</td>
	</tr>
</table>



## License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

## Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md).
