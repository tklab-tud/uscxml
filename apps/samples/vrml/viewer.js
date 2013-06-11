function VRMLViewer(element, params) {

  // private attributes
  var self = this;
  
  // private instanceId
  if (!VRMLViewer.instances)
    VRMLViewer.instances = 0;
  this.instanceId = VRMLViewer.instances++;
  var batchChanges = false;
  
  // public attributes
  this.width       = 450;
  this.height      = 350;
  
  this.pose = {};
  this.pose.pitch       = 0;
  this.pose.roll        = 0;
  this.pose.yaw         = 0;
  this.pose.zoom        = 1;
  this.pose.x           = 0;
  this.pose.y           = 0;
  this.pose.z           = 0;
  this.pose.autorotate  = false;
  this.serverURL;
  this.imageURL;
  
  this.pose.width       = this.width;
  this.pose.height      = this.height;
  
  this.params = params;

  // privileged public methods
  this.updateScene = function() {
    if (self.imageURL && !self.batchChanges) {
      self.imgElem.src = self.imageURL + urlSuffixForPose(self.pose);
    }
  }

  var urlSuffixForPose = function(pose) {
    var url =
    '?width=' + pose.width + 
    '&height=' + pose.height +
    '&pitch=' + pose.pitch +
    '&roll=' + pose.roll +
    '&yaw=' + pose.yaw +
    '&x=' + pose.x +
    '&y=' + pose.y +
    '&z=' + pose.z +
    '&zoom=' + pose.zoom +
    '&autorotate=' + (pose.autorotate ? '1' : '0');
    return url;
  }

  var moverRelativeTo = function(mover, container) {
    var containerPos = absolutePosition(container);
    return {
      x: mover.x - containerPos.x, 
      y: mover.y - containerPos.y
    };
  }

  // see http://stackoverflow.com/questions/288699/get-the-position-of-a-div-span-tag
  var absolutePosition = function(el) {
    for (var lx=0, ly=0; el != null; lx += el.offsetLeft, ly += el.offsetTop, el = el.offsetParent);
    return {x: lx,y: ly};
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
      self.refreshServer(serverURL);
    }
    self.imageURL = imageURL;
    self.pose = pose;

    var pitch = (pose.pitch % (2 * 3.14159) + 0.5) * 100;
    var roll = (pose.roll % (2 * 3.14159) + 0.5) * 100;
    var yaw = (pose.yaw % (2 * 3.14159) + 0.5) * 100;
        
    var x = ((pose.x / 100) + 0.5) * 100;
    var y = ((pose.y / 100) + 0.5) * 100;

    var zoom = (((pose.zoom - 1) / 3) + 0.5) * 100;

    self.pitchRollHandlerElem.parentNode.style.right = pitch + "%";
    self.pitchRollHandlerElem.parentNode.style.top = roll + "%";

    self.yawZoomHandlerElem.parentNode.style.right = yaw + "%";
    self.yawZoomHandlerElem.parentNode.style.top = zoom + "%";

    self.xyHandlerElem.parentNode.style.right = x + "%";
    self.xyHandlerElem.parentNode.style.top = y + "%";
    
    self.updateScene();
  }

  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom", 
           "dojo/on",
           "dojox/storage", 
           "dojo/store/Memory", 
           "dojo/store/Observable", 
           "dijit/tree/ObjectStoreModel",
           "dijit/Tree",
           "dijit/form/TextBox",
           "dijit/form/Button",
           "dojox/mobile/ProgressIndicator",
           "dijit/form/DropDownButton",
           "dijit/TooltipDialog",
           "dojo/dnd/Moveable",
           "dojo/ready",
           "dojo/dnd/Source"], 
    function(domConst, 
             xhr, 
             dom, 
             on,
             storage, 
             Memory,
             Observable,
             ObjectStoreModel,
             Tree,
             TextBox,
             Button,
             ProgressIndicator,
             DropDownButton,
             TooltipDialog,
             Moveable,
             ready,
             Source) {

      ready(function() {
        
        if (typeof(element) === 'string') {
          element = dom.byId(element);
        }
        element.style.height = self.pose.height;
        element.style.width = self.pose.width;
        
        self.element = element;
        self.xhr = xhr;
        self.progress = new ProgressIndicator({size:40, center:false});
        self.localStorage = dojox.storage.manager.getProvider();
        self.localStorage.initialize();
        
        // establish our dom
        element.appendChild(domConst.toDom('\
          <table>\
            <tr>\
              <td valign="top">\
                  <div style="position: relative; padding: 0px">\
                    <img class="model" src="img/Tutorial.png" style="z-index: -1; width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px"></img>\
                    <div style="z-index: 1; position: absolute; right: 45%; top: 45%">\
                      <div class="progress"></div>\
                    </div>\
                    <div style="position: absolute; left: 10px; top: 10px">\
                      <table></tr>\
                        <td class="browseDropDown" style="vertical-align: middle"></td>\
                        <td align="right"><button type="button" class="resetButton"></button></td>\
                        <td class="dragHandler" style="vertical-align: middle; padding-top: 4px;"></td>\
                      </tr></table>\
                    </div>\
                    <div style="position: absolute; right: 10px; top: 15%; height: 50%">\
                      <div class="zoomSlide"></div>\
                    </div>\
                    <div style="position: absolute; right: 55%; top: 48%">\
                      <div class="pitchRollHandler" style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px;">\
                        <table>\
                          <tr>\
                            <td><img class="pitchRollHandlerImg" src="img/pitchRoll.png" width="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                            <td><div class="pitchLabel"></div><div class="rollLabel"></div></td>\
                          </tr>\
                        </table>\
                      </div>\
                    </div>\
                    <div style="position: absolute; right: 45%; top: 48%">\
                      <div class="yawZoomHandler" style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px;">\
                        <table>\
                          <tr>\
                            <td><img class="yawZoomHandlerImg" src="img/yawZoom.png" width="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                            <td><div class="yawLabel"></div><div class="zoomLabel"></div></td>\
                          </tr>\
                        </table>\
                      </div>\
                    </div>\
                    <div style="position: absolute; right: 50%; top: 58%">\
                      <div class="xyHandler" style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px;">\
                        <table>\
                          <tr>\
                            <td><img class="xyHandlerImg" src="img/xy.png" width="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                            <td><div class="xLabel"></div><div class="yLabel"></div></td>\
                          </tr>\
                        </table>\
                      </div>\
                    </div>\
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
        self.browseDropDownElem = dojo.query("td.browseDropDown", element)[0];

        self.resetButtonElem = dojo.query("button.resetButton", element)[0];
        self.progressElem = dojo.query("div.progress", element)[0];
        self.pitchRollHandlerElem = dojo.query(".pitchRollHandler", element)[0];
        self.yawZoomHandlerElem = dojo.query(".yawZoomHandler", element)[0];
        self.xyHandlerElem = dojo.query(".xyHandler", element)[0];
        
        self.pitchRollHandler = new Moveable(self.pitchRollHandlerElem);
        self.pitchRollHandler.onMoveStop = function(mover) {
          var handlerImg = dojo.query("img.pitchRollHandlerImg", mover.node)[0];
          var pitchLabel = dojo.query("div.pitchLabel", mover.node)[0];
          var rollLabel = dojo.query("div.rollLabel", mover.node)[0];
          
          pitchLabel.innerHTML = '';
          rollLabel.innerHTML = '';
          
          self.updateScene();
        }
        self.pitchRollHandler.onMoving = function(mover) {
          // mover.node.style.backgroundColor = "rgba(255,255,255,0.5)";
          // mover.node.style.borderRadius = "5px";
          // mover.node.style.mozBorderRadius = "5px";
          // mover.node.style.webkitBorderRadius = "5px";
          var handlerImg = dojo.query(".pitchRollHandlerImg", mover.node)[0];
          var pitchLabel = dojo.query(".pitchLabel", mover.node)[0];
          var rollLabel = dojo.query(".rollLabel", mover.node)[0];
          var offset = moverRelativeTo(handlerImg, self.element);
          
          // self.pose.pitch = self.pose.pitch % (2 * 3.14159);
          // self.pose.roll = self.pose.roll % (2 * 3.14159);
          self.pose.roll =  offset.x / self.pose.width - 0.5;
          self.pose.pitch = offset.y / self.pose.height - 0.5;
          self.pose.roll *= 2 * 3.14159;
          self.pose.pitch *= 2 * 3.14159;
          self.pose.roll = Math.ceil((self.pose.roll) * 10) / 10;
          self.pose.pitch = Math.ceil((self.pose.pitch) * 10) / 10;
          pitchLabel.innerHTML = 'Pitch:' + self.pose.pitch;
          rollLabel.innerHTML =   'Roll:' + self.pose.roll;
        }

        self.yawZoomHandler = new Moveable(self.yawZoomHandlerElem);
        self.yawZoomHandler.onMoveStop = function(mover) {
          var handlerImg = dojo.query("img.yawZoomHandlerImg", mover.node)[0];
          var yawLabel = dojo.query("div.yawLabel", mover.node)[0];
          var zoomLabel = dojo.query("div.zoomLabel", mover.node)[0];
          
          yawLabel.innerHTML = '';
          zoomLabel.innerHTML = '';
          
          self.updateScene();
        }
        self.yawZoomHandler.onMoving = function(mover) {
          var handlerImg = dojo.query("img.yawZoomHandlerImg", mover.node)[0];
          var yawLabel = dojo.query("div.yawLabel", mover.node)[0];
          var zoomLabel = dojo.query("div.zoomLabel", mover.node)[0];
          var offset = moverRelativeTo(handlerImg, self.element);

          // self.pose.pitch = self.pose.pitch % (2 * 3.14159);
          // self.pose.roll = self.pose.roll % (2 * 3.14159);
          self.pose.yaw =  (self.pose.width - offset.x) / self.pose.width - 0.5;
          self.pose.zoom = offset.y / self.pose.height - 0.5;
          self.pose.yaw *= 2 * 3.14159;
          self.pose.zoom = self.pose.zoom * 3 + 1;
          self.pose.zoom = Math.ceil((self.pose.zoom) * 10) / 10;
          self.pose.yaw = Math.ceil((self.pose.yaw) * 10) / 10;
          yawLabel.innerHTML = 'Yaw:' + self.pose.yaw;
          zoomLabel.innerHTML = 'Zoom:' + self.pose.zoom;
        }
        
        self.xyHandler = new Moveable(self.xyHandlerElem);
        self.xyHandler.onMoveStop = function(mover) {
          var handlerImg = dojo.query("img.xyHandlerImg", mover.node)[0];
          var xLabel = dojo.query("div.xLabel", mover.node)[0];
          var yLabel = dojo.query("div.yLabel", mover.node)[0];
          
          xLabel.innerHTML = '';
          yLabel.innerHTML = '';
          
          self.updateScene();
        }
        self.xyHandler.onMoving = function(mover) {
          var handlerImg = dojo.query("img.xyHandlerImg", mover.node)[0];
          var xLabel = dojo.query("div.xLabel", mover.node)[0];
          var yLabel = dojo.query("div.yLabel", mover.node)[0];
          var offset = moverRelativeTo(handlerImg, self.element);
          
          self.pose.x = offset.x / self.pose.width - 0.5;
          self.pose.y = offset.y / self.pose.height - 0.5;
          self.pose.x *= 100;
          self.pose.y *= 100;
          self.pose.y = Math.ceil((self.pose.y) * 10) / 10;
          self.pose.x = Math.ceil((self.pose.x) * 10) / 10;
          xLabel.innerHTML = 'X:' + self.pose.x;
          yLabel.innerHTML = 'Y:' + self.pose.y;
        }
        
        self.createAvatar = function(item, mode) {
          if (mode == 'avatar') {
             // create your avatar if you want
             var avatar = dojo.create( 'div', { innerHTML: item.data });
             var avatarPose = dojo.clone(self.pose);
             avatarPose.width=60;
             avatarPose.height=60;
             var avatarImgUrl = urlSuffixForPose(avatarPose);
             avatar.innerHTML = '<img src=' + self.imageURL + avatarImgUrl + ' /> ';
             item.srcEcc = "VRMLViewer";
             item.iconPoseUrl = self.imageURL + avatarImgUrl;
             item.imageURL = self.imageURL;
             item.serverURL = self.serverURL;
             item.pose = avatarPose;
	         return {node: avatar, data: item, type: item.type};
          }
          console.log(item, mode);
          var handler = dojo.create( 'div', { innerHTML: '<img src="img/drag.png" width="20px" />' });
          return {node: handler, data: item, type: item.type};
        };
        
        self.dragHandler = new Source(dojo.query("td.dragHandler", element)[0], {copyOnly: true, creator: self.createAvatar});
        self.dragHandler.insertNodes(false, [ { } ]);

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
            id: "fileList" + self.instanceId,
            model: self.fileTreeModel,
            persist: false,
            showRoot: false,
            style: "height: 200px;",
            onClick: function(item){
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

        });

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
        });

        self.browseButton = new Button({
          label: "Browse",
          onClick: function(){
            self.refreshServer(self.serverBox.get("value"));
          }
        });

        self.browseDropDownContent = domConst.toDom('<div />');
        self.browseDropDownContent.appendChild(self.serverBox.domNode);
        self.browseDropDownContent.appendChild(self.browseButton.domNode);
        self.browseDropDownContent.appendChild(self.fileList.domNode);

        self.browseToolTip = new TooltipDialog({ content:self.browseDropDownContent, style:"max-height:200px"});
        self.browseDropDown = new DropDownButton({ label: "Files", dropDown: self.browseToolTip });
        self.browseDropDownElem.appendChild(self.browseDropDown.domNode);

        self.resetButton = new Button({
          label: "Reset",
          onClick: function(){
            self.pose.x = 0;
            self.pose.y = 0;
            self.pose.pitch = 0;
            self.pose.roll = 0;
            self.pose.yaw = 0;
            self.pose.zoom = 1;
            
            self.xyHandler.node.style.left = 0;
            self.xyHandler.node.style.top = 0;
            self.pitchRollHandler.node.style.left = 0;
            self.pitchRollHandler.node.style.top = 0;
            self.yawZoomHandler.node.style.left = 0;
            self.yawZoomHandler.node.style.top = 0;

            self.updateScene();
          }
        }, self.resetButtonElem);

        // do we have parameters for the initial pose?
        if(self.params)
          self.setPose(self.params.imageURL, self.params.pose, self.params.serverURL);

        var savedServerURL = self.localStorage.get("vrmlServer");
        if (savedServerURL && !self.serverURL) {
          self.serverURL = savedServerURL;
          self.serverBox.value = savedServerURL;
          self.refreshServer(savedServerURL);
        }

      })      
    });


}
