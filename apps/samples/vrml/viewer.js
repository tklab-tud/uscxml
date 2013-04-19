function VRMLViewer(element, params) {

  // private attributes
  var self = this;

  // private instanceId
  if (!VRMLViewer.instances)
    VRMLViewer.instances = 0;
  var instanceId = VRMLViewer.instances++;
  var batchChanges = false;
  
  // public attributes
  this.pose = {};
  this.pose.pitch       = 0;
  this.pose.roll        = 0;
  this.pose.yaw         = 0;
  this.pose.zoom        = 1;
  this.pose.x           = 0;
  this.pose.y           = 0;
  this.pose.z           = 0;
  this.pose.width       = 640;
  this.pose.height      = 480;
  this.pose.autorotate  = false;

  this.serverURL = "http://88.69.49.213:8080/vrml";
  this.imageURL;

  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom", 
           "dojox/storage", 
           "dojox/layout/FloatingPane",
           "dojo/store/Memory", 
           "dojo/store/Observable", 
           "dijit/tree/ObjectStoreModel",
           "dijit/Tree",
           "dijit/form/TextBox",
           "dijit/form/Button",
           "dijit/form/NumberSpinner",
           "dijit/form/VerticalSlider",
           "dijit/form/VerticalRuleLabels", 
           "dijit/form/VerticalRule",
           "dijit/form/HorizontalSlider",
           "dojox/mobile/ProgressIndicator",
           "dojo/ready"], 
    function(domConst, 
             xhr, 
             dom, 
             storage, 
             FloatingPane,
             Memory,
             Observable,
             ObjectStoreModel,
             Tree,
             TextBox,
             Button,
             NumberSpinner,
             VerticalSlider,
             VerticalRuleLabels,
             VerticalRule,
             HorizontalSlider,
             ProgressIndicator,
             ready) {

      ready(function() {
        if (typeof(element) === 'string') {
          element = dom.byId(element);
        }
        
        self.element = element;
        self.xhr = xhr;
        self.progress = new ProgressIndicator({size:40, center:false});
        self.localStorage = dojox.storage.manager.getProvider();
        self.localStorage.initialize();
        
        // establish our dom
        element.appendChild(domConst.toDom('\
          <div class="floatPane">\
            <div style="text-align: right"><div class="server" /></div><button type="button" class="browseButton"></button></div>\
            <div style="height: 100%; overflow: auto" class="fileList"></div>\
          </div>\
          <table>\
            <tr>\
              <td valign="top">\
                  <div style="position: relative; padding: 0px">\
                    <img class="model" style="z-index: -1; min-width: ' + self.pose.width + 'px; min-height: ' + self.pose.height + 'px"></img>\
                    <div style="z-index: 1; position: absolute; right: 45%; top: 45%">\
                      <div class="progress"></div>\
                    </div>\
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
        self.messageBox = dojo.query("div.messages", element)[0];
        self.imgElem = dojo.query("img.model", element)[0];
        self.serverBoxElem = dojo.query("div.server", element)[0];
        self.browseButtonElem = dojo.query("button.browseButton", element)[0];
        self.fileListElem = dojo.query("div.fileList", element)[0];

        self.resetButtonElem = dojo.query("button.resetButton", element)[0];
        self.xSpinnerElem = dojo.query("input.xSpinner", element)[0];
        self.ySpinnerElem = dojo.query("input.ySpinner", element)[0];
        self.pitchSlideElem = dojo.query("div.pitchSlide", element)[0];
        self.rollSlideElem = dojo.query("div.rollSlide", element)[0];
        self.yawSlideElem = dojo.query("div.yawSlide", element)[0];
        self.zoomSlideElem = dojo.query("div.zoomSlide", element)[0];
        self.progressElem = dojo.query("div.progress", element)[0];
        self.floatPaneElem = dojo.query("div.floatPane", element)[0];
        
        self.floatPane = new FloatingPane({
           title: "VRML Viewer",
           resizable: true, dockable: false, closable: false,
           style: "position:absolute;top:10;left:10;width:250px;height:300px;z-index: 2",
           id: "floatPane",
        }, self.floatPaneElem);
        self.floatPane.startup();
        
        // setup fileStore for tree list
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
        
        // setup actual tree dijit
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
        //tree.dndController.singular = true;
        
        var savedServerURL = self.localStorage.get("vrmlServer");
        if (savedServerURL) {
          self.serverURL = savedServerURL;
        }
        
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

            self.floatPane.domNode.style.top = "10px";
            self.floatPane.domNode.style.left = "10px";
//            self.floatPane.startup();
            self.floatPane.show();
          }
        }, self.resetButtonElem);

        self.xSpinner = new NumberSpinner({
          value: 0,
          smallDelta: 1,
          constraints: { places:0 },
          style: "width:60px",
          onChange: function(value){
            self.pose.x = value;
            self.updateScene();
          }
        }, self.xSpinnerElem );

        self.ySpinner = new NumberSpinner({
          value: 0,
          smallDelta: 1,
          constraints: { places:0 },
          style: "width:60px",
          onChange: function(value){
            self.pose.y = value;
            self.updateScene();
          }
        }, self.ySpinnerElem );

        self.zSpinner = new NumberSpinner({
          value: 0,
          smallDelta: 1,
          constraints: { places:0 },
          style: "width:60px",
          onChange: function(value){
            self.pose.z = value;
            self.updateScene();
          }
        }, self.zSpinnerElem );

        self.browseButton = new Button({
          label: "Browse",
          onClick: function(){
            self.refreshServer(self.serverBox.get("value"));
          }
        }, self.browseButtonElem);

        // add zoom slider
        self.zoomSlide = new VerticalSlider({
          minimum: 0.001,
          showButtons: false,
          maximum: 1,
          value: 1,
          intermediateChanges: false,
          style: "height: 90%",
          onChange: function(value){
            self.pose.zoom = Math.ceil(value * 1000) / 1000;
            self.updateScene();
          }
        }, self.zoomSlideElem);
        
        // add pitch slider
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
            self.pose.pitch = Math.ceil(value * 100) / 100;
            self.updateScene();
          }
        }, self.pitchSlideElem);

        // add roll slider
        self.rollSlide = new HorizontalSlider({
          minimum: 0,
          showButtons: false,
          maximum: 2 * 3.14159,
          intermediateChanges: false,
          style: "width: 90%",
          onChange: function(value){
            self.pose.roll = Math.ceil(value * 100) / 100;
            self.updateScene();
          }
        }, self.rollSlideElem);

        // add yaw slider
        self.yawSlide = new HorizontalSlider({
          minimum: 0,
          showButtons: false,
          maximum: 2 * 3.14159,
          intermediateChanges: false,
          style: "width: 90%",
          onChange: function(value){
            self.pose.yaw = Math.ceil(value * 100) / 100;
            self.updateScene();
          }
        }, self.yawSlideElem);
        
      })
    });

  // privileged public methods
  this.updateScene = function() {
    if (self.imageURL && !self.batchChanges) {
      self.imgElem.src = self.imageURL + 
      '?width=' + self.pose.width + 
      '&height=' + self.pose.height +
      '&pitch=' + self.pose.pitch +
      '&roll=' + self.pose.roll +
      '&yaw=' + self.pose.yaw +
      '&x=' + self.pose.x +
      '&y=' + self.pose.y +
      '&z=' + self.pose.z +
      '&zoom=' + self.pose.zoom +
      '&autorotate=' + (self.pose.autorotate ? '1' : '0');
    }
  }

  this.refreshServer = function(server) {
    self.serverURL = server;
    self.localStorage.put("vrmlServer", self.serverURL, null);
    self.progressElem.appendChild(self.progress.domNode);
    self.progress.start();
    self.xhr.get({
      // The URL to request
      url: server,
      handleAs:"json",
      headers:{"X-Requested-With":null},
      load: function(result) {
        self.progress.stop();
        for (id in self.fileStore.query) {
          self.fileStore.remove(id);
        }
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

  this.setPose = function(imageURL, pose, serverURL) {
    if (serverURL && serverURL != self.serverURL) {
      refreshServer(serverURL);
    }
    self.imageURL = imageURL;
    self.pose = pose;

    self.batchChanges = true;
//    self.fileList.set('item', imageURL);
    self.xSpinner.set('value',pose.x);
    self.ySpinner.set('value',pose.y);
    self.zSpinner.set('value',pose.z);
    self.pitchSlide.attr('value',pose.pitch);
    self.rollSlide.attr('value',pose.roll);
    self.yawSlide.attr('value',pose.yaw);
    self.zoomSlide.attr('value',pose.zoom);
    self.batchChanges = false;
    updateScene();
  }

/*
  view = "normal";
  // if (params.view == "maximized") {
  //  view = "maximized";
  // }
  
  // if (this.view == "maximized") {
  //     this.width = Math.min(element.clientWidth - 150, 800);
  //  this.height = (this.width * 3) / 4;
  // } else {
  //     this.width = Math.min(element.clientWidth - 50, 800);
  //  this.height = (this.width * 3) / 4; 
  // }
*/

}
