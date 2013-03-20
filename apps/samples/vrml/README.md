# VRML Server

The VRML Server allows clients to retrieve sceneshots of 3D models on the filesystem in a variety of formats.

## General Mode of Operation

The VRML server will monitor its vrml directory recursively for <tt>vrml</tt> and <tt>wrl</tt>
files. Whenever such a file is found, it is converted into a native, binary representation and
saved in the tmp directory. Clients can now access sceneshots of this model by specifying the
desired pose and format.

## Accessing Sceneshots

In the simplest case, a sceneshot is retrieved by simply requested its respective URL on the VRML server:

<tt>http://host/vrml/HARD_MP_VAL_000.png</tt>

All paths start with vrml and then reflect the vrml directory structure as it is being monitored. When a directory
<tt>foo</tt> was added (either by creation or linking) in the vrml directory, its 3D models will be available at:

<tt>http://host/vrml/foo/FANCY_MODEL_000.png</tt>

When you do not pass any parameters, you will get a sceneshot of the model with its largest, axis aligned surface area 
facing the camera. That is, the model will be rotated by multiples of 90deg to show the side of the bounding box which 
has the largest surface area. The implied assumption is that this side is suited to identify the model and its eventual
problems the quickest.

If you do not like the standard sceneshot, you can pass a couple of parameters to adapt most aspects of the scene:

<table>
	<tr><th>Name</th><th>Range</th><th>Description</th></tr>
	<tr><td><tt>pitch</tt></td><td>[0 .. 2&pi;] rad</td><td>Rotation along the x-axis</td></tr>
	<tr><td><tt>roll</tt></td><td>[0 .. 2&pi;] rad</td><td>Rotation along the z-axis</td></tr>
	<tr><td><tt>yaw</tt></td><td>[0 .. 2&pi;] rad</td><td>Rotation along the y-axis</td></tr>
	<tr><td><tt>zoom</tt></td><td>[0 .. &infin;] bounding-sphere units</td><td>Distance of camera to model center</td></tr>
	<tr><td><tt>x</tt></td><td>[-&infin; .. &infin;] OpenGL units</td><td>Translation on x-axis</td></tr>
	<tr><td><tt>y</tt></td><td>[-&infin; .. &infin;] OpenGL units</td><td>Translation on y-axis</td></tr>
	<tr><td><tt>z</tt></td><td>[-&infin; .. &infin;] OpenGL units</td><td>Translation on z-axis (consider using zoom instead)</td></tr>
	<tr><td><tt>width</tt></td><td>[0 .. BIG] pixels</td><td>The width of the image (limited by your GPU)</td></tr>
	<tr><td><tt>height</tt></td><td>[0 .. BIG] pixels</td><td>The height of the image</td></tr>
	<tr><td><tt>autorotate</tt></td><td>[<tt>on</tt> | <tt>off</tt>]</td><td>Whether or not to autorotate first</td></tr>
</table>

<tt>http://host/vrml/HARD_MP_VAL_000.png?pitch=0.3&width=2560&height=1600</tt>

There are some caveats:
<ul>
	<li>With euler angles such as pitch/roll/yaw, a gimbal lock can occur.
	<li>Choosing zoom, x, y or z to big will move the model off the clipping distance.
	<li>width and height have no upper limit, this might be a potential DoS.
	<li>When observing series of models with autorotating on, not every model is guaranteed to start with the same pose.
	<li>The OpenGL units really ought to be expressed in multiples of bounding-sphere units.
</ul>

## REST API

The main purpose of the REST API is to provide clients with a list of available model files.

<table>
	<tr><th>Path</th><th>Type</th><th>Return Value</th><th>Example</th></tr>
	<tr>
		<td><tt>/vrml</tt></td>
		<td><tt>GET</tt></td>
		<td>
			A JSON structure identifying all known models in the hierarchy as found on the filesystem.<br/>
			
			The entries are organized in a tree, reflecting the original locations relative to the vrml
			directory. The suffix of <tt>png</tt> is just one example, supported extensions are ultimately
			defined by the available <a href="http://www.link.de/here">OSG writer plugins</a>, but limited for
			now to <tt>gif</tt>, <tt>jpg</tt>, <tt>png</tt>, <tt>tif</tt> and <tt>bmp</tt>.
		</td>
		<td>
<pre>
{
  "models": {
    "HARD_MP_VAL_000": {
      "path": "/HARD_MP_VAL_000.png", 
      "url": "http://host/vrml/HARD_MP_VAL_000.png"
    }, 
    "HARD_MP_VAL_001": {
      "path": "/HARD_MP_VAL_001.png", 
      "url": "http://host/vrml/HARD_MP_VAL_001.png"
    }, 
    "data": {
      "SOFT_MP_VAL_000": {
        "path": "/data/SOFT_MP_VAL_000.png", 
        "url": "http://host/vrml/data/SOFT_MP_VAL_000.png"
      }, 
  ...
</pre>			
		</td>
	</tr>

	<tr>
		<td><tt>/vrml/models</tt>, <tt>/vrml/wrls</tt></td>
		<td><tt>GET</tt></td>
		<td>
			A JSON structure with information about the available binary model files in the tmp directory or the wrl 
			files in the vrml directory respectively.<br/>

			The entries correspond to the tree at <tt>/vrml</tt> but all paths are flattened using the path delimiter 
			('<tt>:</tt>' per default).
		</td>
		<td>
<pre>
{
  "HARD_MP_VAL_000": {
    "atime":        1363002503, 
    "ctime":        1362521747, 
    "dir":          "/tmp", 
    "extension":    "osgb", 
    "group":        "/", 
    "mtime":        "1362521747", 
    "name":         "HARD_MP_VAL_000.osgb", 
    "path":         "/tmp/HARD_MP_VAL_000.osgb", 
    "relDir":       "/", 
    "relPath":      "/HARD_MP_VAL_000.osgb", 
    "size":         "580201", 
    "strippedName": "HARD_MP_VAL_000"
  }, 
...
</pre>			
		</td>
	</tr>

		<tr>
			<td><tt>/vrml/processed</tt></td>
			<td><tt>GET</tt></td>
			<td>
				A JSON structure with information about the sceneshots that were requested recently and are still on disc.<br/>

				The individual entries within a model key encode the request parameters seperated by underscores, that is:<br/>
				The euler angles <tt>pitch</tt>, <tt>roll</tt>, <tt>yaw</tt>, <tt>zoom</tt>, translation in <tt>x</tt>, translation 
				in <tt>y</tt>, translation in <tt>z</tt>, <tt>width</tt>, <tt>height</tt>, and whether or not to <tt>autorotate</tt>. 
			</td>
			<td>
	<pre>
{
  "HARD_MP_VAL_000": {
    "0.94_0_0_1_0_0_0_640_480_on.png": {
      "atime":        1363002687, 
      "ctime":        1363002687, 
      "dir":          "/tmp", 
...
	</pre>
			</td>
		</tr>


</table>
