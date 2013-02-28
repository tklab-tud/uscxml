# Extensions

## Invokers

Most platform specific extensions are realized via special invokers. These are components that you can load via:

    <invoke type="invokerName" id="something.unique">
      <param name="paramatername" expr="'paramatervalue'">
      <param name="othername" expr="'othervalue'">
      <content>
        <invoker:someXML>
          <invoker:here>
        </invoker:someXML>
      </content>
    </invoke>

When invoked, you can send them events via:

    <send target="#_something.unique">
      <param name="paramatername" expr="'paramatervalue'">
      <param name="othername" expr="'othervalue'">
    </send>

To get an idea which parameters can be passed for invoke and send, the source as linked below is the ultimate reference.

<b>Note:</b> Every <tt>expr</tt> attribute is subject to evaluation by the datamodel. If you want to pass a literal string
with the <tt>ecmascript</tt> datamodel, you will have to 'quote' it.

### FFMPEG
  * <b>[FFMPEGInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/ffmpeg/FFMPEGInvoker.cpp)</b>

### Directory Monitor
  * <b>[DirMonInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.cpp)</b>

Monitors a directory for modifications.

<table>
	<tr><th colspan="4" align="left">Invoke</th></tr>
	<tr><td><tt>type</tt></td><td colspan="3">
		<tt>dirmon</tt><br />
		<tt>DirectoryMonitor</tt><br />
		<tt>http://uscxml.tk.informatik.tu-darmstadt.de/#dirmon</tt>
	</td></tr>
	<tr><th align="left">param</th><th align="left">expr</th><th align="left">default</th><th align="left">comment</th></tr>
	<tr>
		<td><tt>dir</tt></td>
		<td>A valid system directory</td>
		<td>none</td>
		<td>Anything that evaluates to a valid directory with the given datamodel</td>
	</tr>
	<tr>
		<td><tt>recurse</tt></td>
		<td>"true" or "false"</td>
		<td><tt>false</tt></td>
		<td>Whether or not to monitor subdirectories as well.</td>
	</tr>
	<tr>
		<td><tt>suffix</tt><br /><tt>suffixes</tt></td>
		<td>filename suffixes</td>
		<td>all</td>
		<td>A single or space-seperated list of suffixes of files that will get reported</td>
	</tr>
	<tr><td colspan="4"><hr /></td></tr>
	<tr><th colspan="4" align="left">Send</th></tr>
	<tr>
		<td colspan="4">Will not accept anything yet.</td>
	</tr>
	<tr><td colspan="4"><hr /></td></tr>
	<tr><th colspan="4" align="left">Emitted Events</th></tr>
	<tr><td>Example</td><td colspan="3"><pre>
'invokeid' => "dirmon.vrml"
'origintype' => "dirmon"
'origin' => "#_dirmon.vrml"
'name' => "file.existing"
'data' ...
    'file' ...
        'atime' => "1361746741"
        'ctime' => "1350452789"
        'dir' => "/Users/sradomski/data"
        'extension' => "wrl"
        'mtime' => "1328012634"
        'name' => "HARD_MP_VAL_035.wrl"
        'path' => "/Users/sradomski/data/HARD_MP_VAL_035.wrl"
        'relPath' => "/HARD_MP_VAL_035.wrl"
        'size' => "1509110"</pre>
		</td></tr>
	<tr><th align="left">Field</th><th colspan="3" align="left">Details</th></tr>
	<tr><td><tt>name</tt></td>
		<td colspan="3">One of <tt>file.[existing|added|deleted|modified]</tt></td></tr>
	<tr><td><tt>data.file.dir</tt></td>
		<td colspan="3">The directory as passed per <tt>dir</tt> param to invoke.</td></tr>
	<tr><td><tt>data.file.path</tt></td>
		<td colspan="3">The full path to the file we found.</td></tr>
	<tr><td><tt>data.file.relPath</tt></td>
		<td colspan="3">The relative path starting from <tt>data.file.dir</tt> to the file we found.</td></tr>
	<tr><td><tt>data.file.size</tt></td>
		<td colspan="3">File size in bytes.</td></tr>
	
</table>

### 3D Scenegraph
  * <b>[OSGInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/graphics/openscenegraph/OSGInvoker.cpp)</b>

Accepts a simplified scenegraph XML notation as content and opens a set of windows with scenes. This invoker registers 
as an event listener on the XML in the content and will allow changes to the scenegraph per ecmascript.

  * <b>[OSGConverter.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/graphics/openscenegraph/OSGConverter.cpp)</b>

Transfer model files into other representations and make screenshots of models.

### Heartbeat
  * <b>[HeartbeatInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/heartbeat/HeartbeatInvoker.cpp)</b>

Continuously sends events.

<table>
	<tr><th colspan="4" align="left">Invoke</th></tr>
	<tr><td><tt>type</tt></td><td colspan="3">
		<tt>heartbeat</tt><br />
		<tt>http://uscxml.tk.informatik.tu-darmstadt.de/#heartbeat</tt>
	</td></tr>
	<tr><th align="left">param</th><th align="left">expr</th><th align="left">default</th><th align="left">comment</th></tr>
	<tr>
		<td><tt>interval</tt></td>
		<td>e.g. <tt>'3s'</tt> or <tt>'1200ms'</tt></td>
		<td>none</td>
		<td>A time designation as defined in CSS2</td>
	</tr>
	<tr>
		<td><tt>eventname</tt></td>
		<td>The name of the event to send in the given interval</td>
		<td>Defaults to <tt>heartbeat.&lt;interval></tt></td>
		<td></td>
	</tr>
	<tr><td colspan="4"><hr /></td></tr>
	<tr><th colspan="4" align="left">Send</th></tr>
	<tr>
		<td colspan="4">Will not accept anything yet.</td>
	</tr>
	<tr><td colspan="4"><hr /></td></tr>
	<tr><th colspan="4" align="left">Emitted Events</th></tr>
	<tr><td>Example</td><td colspan="3"><pre>
'invokeid' => "heartbeat"
'origintype' => "heartbeat"
'origin' => "#_heartbeat"
'name' => "heartbeat.100ms"
'data' => "undefined"</pre>
		</td></tr>
	<tr><th align="left">Field</th><th colspan="3" align="left">Details</th></tr>
	<tr><td><tt>name</tt></td>
		<td colspan="3">One of <tt>file.[existing|added|deleted|modified]</tt></td></tr>
	<tr><td><tt>data.file.dir</tt></td>
		<td colspan="3">The directory as passed per <tt>dir</tt> param to invoke.</td></tr>
	<tr><td><tt>data.file.path</tt></td>
		<td colspan="3">The full path to the file we found.</td></tr>
	<tr><td><tt>data.file.relPath</tt></td>
		<td colspan="3">The relative path starting from <tt>data.file.dir</tt> to the file we found.</td></tr>
	<tr><td><tt>data.file.size</tt></td>
		<td colspan="3">File size in bytes.</td></tr>
</table>

### HTTP Servlet
  * <b>[HTTPServletInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/http/HTTPServletInvoker.cpp)</b>

### SCXML
  * <b>[HTTPServletInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/scxml/USCXMLInvoker.cpp)</b>

### uMundo Publish / Subscribe
  * <b>[UmundoInvoker.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/invoker/umundo/UmundoInvoker.cpp)</b>

## Elements

### Fetch
  * <b>[FetchElement.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/element/fetch/FetchElement.cpp)</b>

### Postpone
  * <b>[PostponeElement.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/element/postpone/PostponeElement.cpp)</b>

### Response
  * <b>[ResponseElement.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/element/response/ResponseElement.cpp)</b>

## IO Processors

### BasicHTTP
  * <b>[EventIOProcessor.cpp](https://github.com/tklab-tud/uscxml/blob/master/src/uscxml/plugins/ioprocessor/basichttp/libevent/EventIOProcessor.cpp)</b>
