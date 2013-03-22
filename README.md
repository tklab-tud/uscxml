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

## License 

uSCXML itself is distributed under the Simplified BSD license as in, do not sue us and do
not misrepresent authorship. Please have a look at the licenses of the [libraries we depend
upon](https://github.com/tklab-tud/uscxml/blob/master/docs/BUILDING.md#build-dependencies) as well.

## Download

We do not yet feature installers. Please download the source and have a look at the [build
instructions](https://github.com/tklab-tud/umundo/blob/master/docs/BUILDING.md).
