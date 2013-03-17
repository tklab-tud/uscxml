function VRMLViewer(element, params) {
	
	// private attributes
	var self = this;
	var dojo               = require("dojo");
	var domConst           = dojo.require('dojo/dom-construct');
	var xhr                = dojo.require("dojo/_base/xhr");

  require(["dojox/storage"], function (storage) {
    self.localStorage = dojox.storage.manager.getProvider();
    self.localStorage.initialize();
    var savedServerURL = self.localStorage.get("vrmlServer");
    if (savedServerURL) {
      self.serverURL = savedServerURL;
      self.serverBox.set('value', savedServerURL);
    }
  });

	/**
	 * Why can't I fetch dijits via CommonJS?
	 */
  // var Button             = require('dijit/form/Button');
  // var HorizontalSlider   = require('dijit/form/HorizontalSlider');
  // var VerticalSlider     = require('dijit/form/VerticalSlider');
  

  // private instanceId
  if (!VRMLViewer.instances)
  	VRMLViewer.instances = 0;
  var instanceId = VRMLViewer.instances++;
  
  // public attributes
  this.pitch       = 0;
	this.roll        = 0;
	this.yaw         = 0;
	this.zoom        = 1;
	this.x           = 0;
	this.y           = 0;
	this.z           = 0;
	this.width       = 640;
	this.height      = 480;
	this.autorotate  = false;

  this.serverURL = "http://88.69.49.213:8080/vrml";
  this.imageURL;

	view = "normal";
	if (params.view == "maximized") {
		view = "maximized";
	}
	
  // if (this.view == "maximized") {
  //     this.width = Math.min(element.clientWidth - 150, 800);
  //  this.height = (this.width * 3) / 4;
  // } else {
  //     this.width = Math.min(element.clientWidth - 50, 800);
  //  this.height = (this.width * 3) / 4; 
  // }

	// privileged public methods
	this.updateScene = function() {
	  if (self.imageURL) {
  	  self.imgElem.src = self.imageURL + 
  	    '?width=' + self.width + 
  	    '&height=' + self.height +
  	    '&pitch=' + self.pitch +
  	    '&roll=' + self.roll +
  	    '&yaw=' + self.yaw +
  	    '&x=' + self.x +
  	    '&y=' + self.y +
  	    '&z=' + self.z +
  	    '&zoom=' + self.zoom +
  	    '&autorotate=' + (self.autorotate ? '1' : '0');
      }
	}

	this.refreshServer = function(server) {
    serverURL = server;
    self.localStorage.put("vrmlServer", serverURL, null);
    xhr.get({
        // The URL to request
        url: server,
        handleAs:"json",
        headers:{"X-Requested-With":null},
        load: function(result) {
            (function fillstore(tree, parentId) {
              for (key in tree) {
                if ('url' in tree[key]) {
                  self.fileStore.add({id:parentId+key, name:key, url:self.serverURL + tree[key].path, parent:parentId});
//                  self.messageBox.innerHTML += '<pre>' + self.serverURL + tree[key].path + '</pre>';
//                  self.messageBox.innerHTML += '<pre>' + tree[key].url + '?width=200&height=150</pre>' + '<img src="' + tree[key].url + '?width=200&height=150" />';
                } else {
                  self.fileStore.add({id:parentId+key, name:key, parent:parentId});
                  fillstore(tree[key], parentId+key);
                }
              }
            } (result.models, "root", ""));
        }
    });
	}

  // establish our dom
	element.appendChild(domConst.toDom('\
	  <div id="floatPane">\
	    <div style="text-align: right"><div class="server" /></div><button type="button" class="browseButton"></button></div>\
		  <div style="height: 100%; overflow: auto" class="fileList"></div>\
	  </div>\
		<table>\
			<tr>\
				<td valign="top">\
						<div style="position: relative; padding: 0px">\
						  <img class="model" style="z-index: -1; min-width: ' + self.width + 'px; min-height: ' + self.height + 'px"></img>\
  						<div style="position: absolute; left: 10px; top: 7%; height: 100%">\
  						  <div class="pitchSlide"></div>\
  					  </div>\
  						<div style="position: absolute; right: 10px; top: 15%; height: 50%">\
  						  <div class="zoomSlide"></div>\
  					  </div>\
						  <div style="position: absolute; left: 7%; top: 10px; width: 100%">\
  							<div class="rollSlide"></div>\
  						</div>\
  						<div style="position: absolute; left: 7%; bottom: 15px;">\
  							<div class="yawSlide"></div>\
  						</div>\
  						<table cellspacing="0" style="position: absolute; right: 5px; bottom: 25px">\
  						  <tr>\
			            <td align="right">x: <input type="text" class="xSpinner"></input></td>\
  						  </tr>\
  						  <tr>\
				          <td align="right">y: <input type="text" class="ySpinner"></input></td>\
  						  </tr>\
  						  <tr>\
						      <td align="right"><button type="button" class="resetButton"></button></td>\
  						  </tr>\
  						</table>\
						</div>\
				</td>\
				<td valign="top" height="100%">\
				</td>\
			</tr>\
		  <tr>\
			  <td colspan="2"><div class="messages"></div></td>\
			</tr>\
		</table>\
	'));

  // fetch special dom nodes for content
	this.messageBox = dojo.query("div.messages", element)[0];
	this.imgElem = dojo.query("img.model", element)[0];
	this.serverBoxElem = dojo.query("div.server", element)[0];
	this.browseButtonElem = dojo.query("button.browseButton", element)[0];
	this.fileListElem = dojo.query("div.fileList", element)[0];

	this.resetButtonElem = dojo.query("button.resetButton", element)[0];
	this.xSpinnerElem = dojo.query("input.xSpinner", element)[0];
	this.ySpinnerElem = dojo.query("input.ySpinner", element)[0];
	this.pitchSlideElem = dojo.query("div.pitchSlide", element)[0];
	this.rollSlideElem = dojo.query("div.rollSlide", element)[0];
	this.yawSlideElem = dojo.query("div.yawSlide", element)[0];
	this.zoomSlideElem = dojo.query("div.zoomSlide", element)[0];
  
  require(["dojox/layout/FloatingPane"], function(FloatingPane) {
    self.floatPane = new FloatingPane({
       title: "VRML Viewer",
       resizable: true, dockable: false, closable: false,
       style: "position:absolute;top:10;left:10;width:250px;height:300px;z-index: 2",
       id: "floatPane",
    }, dojo.byId("floatPane"));

    self.floatPane.startup();
  });

  // require(['dijit/form/Button','dijit/Dialog'],
  //   function (Button) {
  //     var d = new Dialog({
  //                     'title':'I am nonmodal',
  //                     'class':'nonModal'
  //                   });
  //   });

  // setup fileStore for tree list
  require(["dojo/store/Memory", "dojo/store/Observable", "dijit/tree/ObjectStoreModel"], 
    function(Memory, Observable, ObjectStoreModel){
    self.fileStore = new Observable(new Memory({
      data: [ { id: 'root', name:'3D Models'} ],
      getChildren: function(object){
          return this.query({parent: object.id});
      }
    }));    
    self.fileTreeModel = new ObjectStoreModel({
        store: self.fileStore,
        query: { id: "root" }
    });
  });

  // setup actual tree dijit
  require(["dojo/dom", "dojo/store/Memory", "dojo/store/Observable", "dijit/tree/ObjectStoreModel", "dijit/Tree"], 
    function(dom, Memory, Observable, ObjectStoreModel, Tree) {
      self.fileList = new dijit.Tree({
          id: "fileList",
          model: self.fileTreeModel,
          persist: false,
          showRoot: false,
          onClick: function(item){
//              self.messageBox.innerHTML = '<pre>' + item.url + '?width=200&height=150</pre>' + '<img src="' + item.url + '?width=200&height=150" />';
              if ('url' in item) {
                self.imageURL = item.url;
                self.updateScene();
              }
          },
          getIconClass: function(item, opened) {
              return (!item || !('url' in item)) ? (opened ? "dijitFolderOpened" : "dijitFolderClosed") : "dijitLeaf"
          },
          getIconStyle: function(item, opened){
            if('url' in item) {
              return { backgroundImage: "url('" + item.url + "?width=16&height=16')"};
            }
          }
          //return {backgroundImage: "url('" + item.url + "?width=16&height=16')"};
          
      }).placeAt(self.fileListElem);
//      tree.dndController.singular = true;
  });
  
  require(["dijit/form/TextBox"], function(TextBox) {
  	self.serverBox = new TextBox({
      name: "Server",
      value: self.serverURL,
  		style: "width: 70%",
  		
  		onKeyDown: function(e) {
        var code = e.keyCode || e.which;
        if( code === 13 ) {
          e.preventDefault();
    		  self.refreshServer(this.get("value"));
          return false; 
        }
  		},
  	}, self.serverBoxElem);
  });

  require(["dijit/form/Button"], function(Button) {
  	self.resetButton = new Button({
      label: "Reset",
  		onClick: function(){
  		  self.xSpinner.set('value',0);
  		  self.ySpinner.set('value',0);
  		  self.zSpinner.set('value',0);
  		  self.pitchSlide.attr('value',0);
  		  self.rollSlide.attr('value',0);
  		  self.yawSlide.attr('value',0);
  		  self.zoomSlide.attr('value',1);

  		  self.floatPane.startup();
  		  self.floatPane.show();
  		}
  	}, self.resetButtonElem);
  });

  require(["dijit/form/NumberSpinner"], function(NumberSpinner) {
    self.xSpinner = new NumberSpinner({
      value: 0,
      smallDelta: 1,
      constraints: { places:0 },
      style: "width:60px",
      onChange: function(value){
      	self.x = value;
      	self.updateScene();
      }
    }, self.xSpinnerElem );
  });

  require(["dijit/form/NumberSpinner"], function(NumberSpinner) {
    self.ySpinner = new NumberSpinner({
      value: 0,
      smallDelta: 1,
      constraints: { places:0 },
      style: "width:60px",
      onChange: function(value){
      	self.y = value;
      	self.updateScene();
      }
    }, self.ySpinnerElem );
  });

  require(["dijit/form/NumberSpinner"], function(NumberSpinner) {
    self.zSpinner = new NumberSpinner({
      value: 0,
      smallDelta: 1,
      constraints: { places:0 },
      style: "width:60px",
      onChange: function(value){
      	self.z = value;
      	self.updateScene();
      }
    }, self.zSpinnerElem );
  });

  require(["dijit/form/Button"], function(Button) {
	  self.browseButton = new Button({
      label: "Browse",
  		onClick: function(){
  		  self.refreshServer(self.serverBox.get("value"));
  		}
  	}, self.browseButtonElem);
  });

	// add zoom slider
  require(["dijit/form/VerticalSlider"], function(VerticalSlider) {
  	self.zoomSlide = new VerticalSlider({
  		minimum: 0.001,
  		showButtons: false,
  		maximum: 1,
  		value: 1,
  		intermediateChanges: false,
  		style: "height: 90%",
      onChange: function(value){
      	self.zoom = Math.ceil(value * 1000) / 1000;
      	self.updateScene();
      }
  	}, self.zoomSlideElem);
	});

	// add pitch slider
  require(["dijit/form/VerticalSlider", "dijit/form/VerticalRuleLabels", "dijit/form/VerticalRule"], function(VerticalSlider, VerticalRuleLabels, VerticalRule) {
    // Create the rules
    // var rulesNode = dojo.create("div", {}, self.pitchSlideElem, "first");
    // var sliderRules = new VerticalRule({
    //   container: "leftDecoration",
    //   count: 11,
    //   style: "width: 5px;"}, rulesNode);

    // Create the labels
    // var labelsNode = dojo.create(
    //   "div", {}, self.pitchSlideElem, "first");
    // var sliderLabels = new VerticalRuleLabels({
    //   labels: ["Pitch", ""],
    //   container: "rightDecoration",
    //   labelStyle: "-webkit-transform: rotate(-90deg); -moz-transform: rotate(-90deg); padding-left: -3px; font-size: 0.75em"
    // }, labelsNode);

  	self.pitchSlide = new VerticalSlider({
  		minimum: 0,
  		showButtons: false,
  		maximum: 2 * 3.14159,
  		value: 0,
  		intermediateChanges: false,
  		style: "height: 90%",
      onChange: function(value){
      	self.pitch = Math.ceil(value * 100) / 100;
      	self.updateScene();
      }
  	}, self.pitchSlideElem);
	});
	
	// add roll slider
  require(["dijit/form/HorizontalSlider"], function(HorizontalSlider) {
  	self.rollSlide = new HorizontalSlider({
  		minimum: 0,
  		showButtons: false,
  		maximum: 2 * 3.14159,
  		intermediateChanges: false,
  		style: "width: 90%",
  		onChange: function(value){
  			self.roll = Math.ceil(value * 100) / 100;
				self.updateScene();
  		}
  	}, self.rollSlideElem);
	});

	// add yaw slider
  require(["dijit/form/HorizontalSlider"], function(HorizontalSlider) {
  	self.yawSlide = new HorizontalSlider({
  		minimum: 0,
  		showButtons: false,
  		maximum: 2 * 3.14159,
  		intermediateChanges: false,
  		style: "width: 90%",
  		onChange: function(value){
  			self.yaw = Math.ceil(value * 100) / 100;
				self.updateScene();
  		}
  	}, self.yawSlideElem);
	});
  
}
