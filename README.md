# uSCXML ReadMe

uSCXML is a SCXML interpreter written in C/C++. It is still in a rather early stage but mostly
feature-complete as far as the W3C SCXML draft specifies. It runs on most <b>Linux</b>,
<b>Windows</b> and <b>MacOSX</b>, each 32- as well as 64Bits. 

There is no technical reason for it not to run on iOS and Android as well, but we did not yet setup
the respective build-process.

   * <b>Datamodels</b>
       * ECMAScript using Google's v8 and JavaScriptCore (JSC is incomplete)
       * Prolog using SWI prolog
   * <b>Invokers</b>
       * <tt>scxml</tt>: Invoke a nested scxml interpreter
       * <tt>dirmon</tt>: Watches a directory for changes to files
       * <tt>scenegraph</tt>: Simplified 3D scenegraphs with custom markup
       * <tt>heartbeat</tt>: Periodically sends events
       * <tt>httpservlet</tt>: Sends events for http requests to special paths
       * <tt>umundo</tt>: Subscribe to channels and publish events
   * <b>DOM</b>
       * DOM Core Level 2 + XPath extensions available for ecmascript datamodel
       * Namespace aware to embed custom markup for special invokers
   * <b>Communication</b>
       * Features the standard basichttp io-processor
       * Can actually respond to HTTP requests with data via &lt;response>
   * <b>Language Bindings</b>
       * PHP module for apache and cli interpreter

## Test Reports

<b>[Results](http://uscxml.tk.informatik.tu-darmstadt.de/cdash/index.php?project=uscxml)</b> for continuous testing of the 
[W3C IRP tests](http://www.w3.org/Voice/2013/scxml-irp/) for SCXML and some platform tests.

<table>
	<tr><th>Test#</th><th>Status</th><th>Comment</th></tr>
	<tr><td><tt>178</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td>A manual test that relies on an unspecified _event.raw attribute</td>
	<tr><td><tt>230</tt></td><td><tt>False report</tt></td>
		<td>A manual test that is not actually failing but does not end in a state called <tt>pass</tt></td>
	<tr><td><tt>250</tt></td><td><tt>False report</tt></td>
		<td>A manual test that is not actually failing but does not end in a state called <tt>pass</tt></td>
	<tr><td><tt>301</tt></td><td><tt>Failed</tt></td>
		<td><i>"If the script can not be downloaded within a platform-specific timeout interval, the document 
			is considered non-conformant, and the platform must reject it"</i> -- USCXML will try to evaluate the 
			rest of the document nevertheless.</td>
	</tr>
	<tr><td><tt>307</tt></td><td><tt>False report</tt></td>
		<td>A manual test that is not actually failing but does not end in a state called <tt>pass</tt></td>
	<tr><td><tt>329</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td>Tests that <tt>_event</tt> cannot be assigned, but I like to add attributes to _event to have a 
			scope that only lasts for one event. Will raise the issue on the ML.</td>
	<tr><td><tt>333</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td><i>"sendid [...] Otherwise it must leave it blank."</i> -- USCXML sets this to the empty string instead of <tt>null</tt>.</td>
	<tr><td><tt>335</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td><i>"origin [...] For internal and platform events, the Processor must leave this field blank."</i> -- USCXML sets this to the empty string instead of <tt>null</tt>.</td>
	<tr><td><tt>337</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td><i>"origintype [...] For internal and platform events, the Processor must leave this field blank."</i> -- USCXML sets this to the empty string instead of <tt>null</tt>.</td>
	<tr><td><tt>339</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td><i>"invokeid [...] Otherwise it must leave it blank."</i> -- USCXML sets this to the empty string instead of <tt>null</tt>.</td>
	<tr><td><tt>346</tt></td><td><tt>Failed / Won't&nbsp;fix</tt></td>
		<td><i>"test that any attempt to change the value of a system variable causes error.execution to be raised."</i> -- I like to edit _event.</td>

</table>



## License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

## Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/umundo/blob/master/docs/BUILDING.md).
