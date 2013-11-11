function VRMLViewer(element, params) {

  // private attributes
  var self = this;
  var batchChanges = false;
  var webGLManipulatorsSetup = false;
  
  // private instanceId
  if (!VRMLViewer.instances)
    VRMLViewer.instances = 0;
  this.instanceId = VRMLViewer.instances++;
  
  // public attribute defaults
  this.width       = 450;
  this.height      = 350;
  
  {
    var pose = {
      pitch: 0,
      roll: 0,
      yaw: 0,
      zoom: 1,
      x: 0,
      y: 0,
      z: 0,
      width: this.width,
      height: this.height,
      autorotate: false,
    }
    this.pose = pose;
  }
  
  this.enableMovies = true;
  this.enableDND = true;
  this.enableWebGL = false;
  this.enableSceneshots = true;
  this.enableDraggables = true;
  this.treeNavigationStyle = true;
  this.listNavigationStyle = true;
  this.listDirectory = "";

  this.serverURL = "localhost:8080";
  this.imagePath = "";
  this.imageFormat = ".png";
  this.resRoot = "";
  
  // copy over values from constructor arguments
  if (params) {
    for (var param in params) {
      if (self.hasOwnProperty(param)) {
        self[param] = params[param];
      } else {
        console.log("Unknown paramter " + param);
      }
    }
  }
  
  var hasWebGL = function() {
    try {
      if (!window.WebGLRenderingContext) {
         return false;
      }
      var canvas = document.createElement("canvas");
      var names = ["webgl", "experimental-webgl", "moz-webgl", "webkit-3d"];
      for (var i = 0; i < 4; i++) {
        var gl = canvas.getContext(names[i]);
        if (gl) {
          return true;
        }
      }
    } catch(e) {
      return false;
    }
    return false;
  }
  
  if (self.enableWebGL && !hasWebGL()) {
    console.log("Your browser does no support WebGL, falling back to sceneshots");
    self.enableWebGL = false;
    self.enableSceneshots = true;
  }
  
  // normalize parameters
  var normalizeParams = function() {
    // make sure server url begins with protocol and does *not* ends in /
    if (!self.serverURL.substring(0, 7) == "http://" && 
        !self.serverURL.substring(0, 8) == "https://")
      self.serverURL = "http://" + self.serverURL;
    if (!self.serverURL.lastIndexOf("/") === self.serverURL.length)
      self.serverURL += self.serverURL.substring(0, self.serverURL - 1);

    // make sure we have a listDirectory with navigation style list ending in /
    if (self.modelNavigationStyle === "list" && !self.listDirectory && self.imagePath)
      self.listDirectory = self.imagePath.substring(0, self.imagePath.lastIndexOf("/"));
    if (!self.listDirectory.indexOf("/", self.listDirectory.length - 1) !== -1)
      self.listDirectory += "/";
  
    // use latest image if none given
    if (!self.imagePath)
      self.imagePath = self.listDirectory + "latest";
  
    if (!self.imageFormat.substring(0, 1) != ".")
      self.imageFormat = "." + self.imageFormat;
  }
  normalizeParams();
  
  var getWebGLModel = function(url) {
    var defer = osgDB.Promise.defer();
    var node = new osg.MatrixTransform();
    //node.setMatrix(osg.Matrix.makeRotate(-Math.PI/2, 1,0,0, []));
    var loadModel = function(url) {
      osg.log("loading " + url);
      var req = new XMLHttpRequest();
      req.open('GET', url, true);
      req.onreadystatechange = function(aEvt) {
        if (req.readyState == 4) {
          if(req.status == 200) {
            osgDB.Promise.when(osgDB.parseSceneGraph(JSON.parse(req.responseText))).then(function(child) {
              node.setMatrix(osg.Matrix.makeRotate(Math.PI/2.0, 1,0,0,[]));
              node.addChild(child);
              defer.resolve(node);
              osg.log("success " + url);
            });
          } else {
            osg.log("error " + url);            
          }
        }
      };
      req.send(null);
    };
    loadModel(url);
    return defer.promise;
  }

  var urlSuffixForPose = function(pose) {
    var queryString =
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
    return queryString;
  };

  var moverRelativeTo = function(mover, container) {
    var containerPos = absolutePosition(container);
    return {
      x: mover.x - containerPos.x, 
      y: mover.y - containerPos.y
    };
  };

  // see http://stackoverflow.com/questions/288699/get-the-position-of-a-div-span-tag
  var absolutePosition = function(el) {
    for (var lx=0, ly=0; el != null; lx += el.offsetLeft, ly += el.offsetTop, el = el.offsetParent);
    return {x: lx,y: ly};
  };

  // update the scene
  this.updateScene = function() {
    if (self.serverURL && self.imagePath && !self.batchChanges) {
      console.log(self.serverURL + self.imagePath + self.imageFormat + urlSuffixForPose(self.pose));
      if (self.enableWebGL) {
        osgDB.Promise.when(getWebGLModel(self.serverURL + self.imagePath + '.osgjs')).then(function(model) {       
          self.webGLViewer.setSceneData(model);
          if (!webGLManipulatorsSetup) {
            self.webGLViewer.setupManipulator();
            self.webGLViewer.getManipulator().computeHomePosition();  
          }
          webGLManipulatorsSetup = true;
      	});
      } 
      if (self.enableSceneshots) {
        self.imgElem.src = self.serverURL + self.imagePath + self.imageFormat + urlSuffixForPose(self.pose);
        if (self.enableMovies) {
          // we are showing an image, activate movie controls
          self.movieAddButton.domNode.style.display = "";
          self.movieDropDown.domNode.style.display = "";
        }
      }
    }
  };

  // get list of supported ffmpeg codecs from server
  this.populateMovieCodecs = function(server, selectElem) {
    self.xhr.get({
      // The URL to request
      url: server,
      handleAs:"json",
      headers:{"X-Requested-With":null},
      load: function(result) {
        for (var codec in result.video) {
          if (codec !== "mpeg1video" && 
              codec !== "mpeg2video" && 
              codec !== "mpeg4" && 
              codec !== "h264" && 
              codec !== "ayuv" && 
              codec !== "flashsv" && 
              codec !== "flashsv2" && 
              codec !== "flv" && 
              codec !== "rv40" && 
              codec !== "theora" && 
              codec !== "v210" && 
              codec !== "v308" && 
              codec !== "v408" && 
              codec !== "v410" && 
              codec !== "wmv3" && 
              codec !== "y41p" && 
              codec !== "yuv4")
            continue;
          //console.log(codec);
          selectElem.options.push({ label: result.video[codec].longName, value: codec });              
          if (codec === "mpeg4")
            selectElem.options[selectElem.options.length - 1].selected = true;
        }
      }
    });
  }

  // update list of vrml files from server
  this.refreshServer = function(server, params) {
    self.serverURL = server;
    if (!params)
      params = {};
    if (self.fileStandby) { self.fileStandby.show(); }
    
    self.xhr.get({
      // The URL to request
      url: server,
      handleAs:"json",
      headers:{"X-Requested-With":null},
      error: function(result) {
        
        if (self.browseButton) { self.browseButton.setAttribute('label', 'Browse'); }
        if (self.fileStandby) { self.fileStandby.hide(); }

        if (!params.skipTree) {
          if (self.fileTreeStore) {
            var allItems = self.fileTreeStore.query();
            for (var i = 0; i < allItems.total; i++) {
              self.fileTreeStore.remove(allItems[i].id);          
            }
          }
        }
        if (!params.skipList) {
          if (self.fileListStore) {
            var allItems = self.fileListStore.query();
            for (var i = 0; i < allItems.total; i++) {
              self.fileListStore.remove(allItems[i].id);          
            }
          }
        }
      },
      load: function(result) {
//        self.localStorage.put("vrmlServer", self.serverURL, null);
        if (self.browseButton) { self.browseButton.setAttribute('label', 'Refresh'); }
        if (self.fileStandby) { self.fileStandby.hide(); }

        if (self.treeNavigationStyle && !params.skipTree) {
          // empty store
          var allItems = self.fileTreeStore.query();
          for (var i = 0; i < allItems.total; i++) {
            self.fileTreeStore.remove(allItems[i].id);          
          }
          
          // parse result as tree
          (function fillstore(tree, parentId) {
            // todo: respect navigation style
            for (key in tree) {
              if ('url' in tree[key]) {
                self.fileTreeStore.add({id:parentId+key, name:key, url:tree[key].path, parent:parentId});
              } else {
                self.fileTreeStore.add({id:parentId+key, name:key, parent:parentId});
                fillstore(tree[key], parentId+key);
              }            
            }
          } (result.models, "root", ""));
        }  
        if (self.listNavigationStyle && !params.skipList) {
          
          // empty store
          var allItems = self.fileListStore.query();
          for (var i = 0; i < allItems.total; i++) {
            self.fileListStore.remove(allItems[i].id);          
          }
          
          // parse result as list
          if (!self.listDirectory)
            console.log("Requested modelNavigationStyle === list but provided no listDirectory");
          var dirs = self.listDirectory.split("/");
          var models = result.models;
          for (var dir in dirs) {
            if (!dirs[dir].length)
              continue;
            if (dirs[dir] in models) {
              models = models[dirs[dir]];
            } else {
              console.log("No " + dirs[dir] + " in " + models);
            }
          }
          for (var key in models) {
            var url = self.serverURL + models[key].path;
            self.fileListStore.add({id:key, value:models[key].path, label:key, name:key, url:url});
          }
          self.fileListSelect.startup();
        }
        //self.updateScene();
      }
    });
  };

  this.setPose = function(imagePath, imageFormat, pose, serverURL) {
    if (serverURL && serverURL != self.serverURL) {
      self.refreshServer(serverURL);
    }
    self.imagePath = imagePath;
    self.imageFormat = imageFormat;
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
  };

  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom", 
           "dojo/on",
           "dojo/_base/array",
           "dojox/storage", 
           "dojo/store/Memory", 
           "dojo/store/Observable", 
           "dijit/tree/ObjectStoreModel",
           "dojo/data/ObjectStore",
           "dijit/Tree",
           "dijit/form/TextBox",
           "dijit/form/Button",
           "dojox/widget/Standby",
           "dijit/form/DropDownButton",
           "dijit/TooltipDialog",
           "dojo/dnd/Moveable",
           "dojo/ready",
           "dojo/dnd/Source",
           "dijit/form/HorizontalSlider",
           "dijit/form/Select",
           "dijit/form/NumberSpinner"], 
    function(domConst, 
             xhr, 
             dom, 
             on,
             array,
             storage, 
             Memory,
             Observable,
             ObjectStoreModel,
             ObjectStore,
             Tree,
             TextBox,
             Button,
             Standby,
             DropDownButton,
             TooltipDialog,
             Moveable,
             ready,
             Source,
             HorizontalSlider,
             Selector,
             NumberSpinner) {

      ready(function() {
        
        if (typeof(element) === 'string') {
          element = dom.byId(element);
        }
        element.style.height = self.pose.height;
        element.style.width = self.pose.width;
        
        self.element = element;
        self.xhr = xhr;
        
        // establish our dom
        element.appendChild(domConst.toDom('\
          <table>\
            <tr>\
              <td valign="top">\
                  <div style="position: relative; padding: 0px; width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px">\
                    <div class="screenShot" style="position: absolute; width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px">\
                        <img class="screenShot" style="width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px"></img>\
                    </div>\
                    <div class="webGL" style="position: absolute; width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px">\
                        <canvas class="webGL" style="width: ' + self.pose.width + 'px; height: ' + self.pose.height + 'px"></canvas>\
                    </div>\
                    <div style="z-index: -1; position: absolute; right: 45%; top: 45%">\
                      <div class="progress"></div>\
                    </div>\
                    <div style="position: absolute; left: 10px; top: 10px">\
                      <table></tr>\
                        <td class="treeNavigation filesDropDown" style="vertical-align: middle"></td>\
                        <td class="movieControls">\
                          <div class="movieDropDown" style="display: inline"></div>\
                          <button type="button" class="movieAddButton"></button>\
                        </td>\
                        <td align="right"><button type="button" class="resetButton"></button></td>\
                        <td class="dndHandler" style="vertical-align: middle; padding-top: 4px;"></td>\
                      </tr></table>\
                    </div>\
                    <div style="position: absolute; right: 10px; top: 15%; height: 50%">\
                      <div class="zoomSlide"></div>\
                    </div>\
                    <div class="draggable" style="position: absolute; right: 50%; top: 50%">\
                      <div class="pitchRollHandler" style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px;">\
                        <table>\
                          <tr>\
                            <td><img class="pitchRollHandlerImg" src="' + self.resRoot + 'img/pitchRoll-handle.png" height="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                            <td><div class="pitchLabel"></div><div class="rollLabel"></div></td>\
                          </tr>\
                        </table>\
                      </div>\
                    </div>\
                    <div class="draggable"style="position: absolute; right: 50%; top: 50%">\
                      <div class="yawZoomHandler">\
                        <div style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px; position: absolute; left: -34px;">\
                          <table>\
                            <tr>\
                              <td><img class="yawZoomHandlerImg" src="' + self.resRoot + 'img/yawZoom-handle.png" height="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                              <td><div class="yawLabel"></div><div class="zoomLabel"></div></td>\
                            </tr>\
                          </table>\
                        </div>\
                      </div>\
                    </div>\
                    <div class="draggable"style="position: absolute; right: 50%; top: 50%">\
                      <div class="xyHandler" style="font-size: 0.5em; background-color: rgba(255,255,255,0.5); border-radius: 5px; moz-border-radius: 5px;">\
                        <table>\
                          <tr>\
                            <td><img class="xyHandlerImg" src="' + self.resRoot + 'img/xy-handle.png" width="20px" style="padding: 2px 0px 0px 4px;" /></td>\
                            <td><div class="xLabel"></div><div class="yLabel"></div></td>\
                          </tr>\
                        </table>\
                      </div>\
                    </div>\
                    <div class="listNavigation" style="position: absolute; left: 10px; bottom: 10px">\
                      <table></tr>\
                        <td style="vertical-align: middle"><button class="prevButton" type="button" /></td>\
                        <td style="vertical-align: middle"><div class="fileList" /></td>\
                        <td style="vertical-align: middle"><button class="nextButton" type="button" /></td>\
                      </tr></table>\
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
        self.imgElem = dojo.query("img.screenShot", element)[0];

        /**
         * === WebGL ====================
         */
        var activateWebGL = function(enable) {
          if (enable) {
            self.canvasElem = dojo.query("canvas.webGL", element)[0];
            self.canvasElem.style.width = self.width;
            self.canvasElem.style.height = self.height;
            self.canvasElem.width = self.width;
            self.canvasElem.height = self.height;
            
            // osgDB.Promise.when(getWebGLModel('http://localhost:8081/vrml/cranehook/cranehook_bad_convergence/HARD_MP_VAL_013.osgjs')).then(function(model) {
            //   self.webGLViewer = new osgViewer.Viewer(self.canvasElem, {antialias : true, alpha: true });
            //   self.webGLViewer.init();
            //   self.webGLViewer.getCamera().setClearColor([0.0, 0.0, 0.0, 0.0]);
            //   self.webGLViewer.setSceneData(model);
            //   self.webGLViewer.setupManipulator();
            //   self.webGLViewer.getManipulator().computeHomePosition();  
            //   self.webGLViewer.run();
            // });
            
            if (self.webGLViewer === undefined) {
              self.webGLViewer = new osgViewer.Viewer(self.canvasElem, {antialias : true, alpha: true });
              self.webGLViewer.init();
              self.webGLViewer.getCamera().setClearColor([0.0, 0.0, 0.0, 0.0]);
              self.webGLViewer.setupManipulator();
              self.webGLViewer.run();
            }
            
            // show elements
            array.forEach(dojo.query(".webGL", element), function(entry, i) {
              entry.style.display = "inline";
            })
          } else {
            if (self.webGLViewer) {
              self.webGLViewer.stop();
            }
            // hide elements
            array.forEach(dojo.query(".webGL", element), function(entry, i) {
              entry.style.display = "none";
            })
          }
        }
        activateWebGL(self.enableWebGL);

        var activateScreenshot = function(enable) {
          if (enable) {
            array.forEach(dojo.query(".screenShot", element), function(entry, i) {
              entry.style.display = "inline";
            });
          } else {
            array.forEach(dojo.query(".screenShot", element), function(entry, i) {
              entry.style.display = "none";
            });
          }
        }
        activateScreenshot(self.enableSceneshots);
        
        /**
         * === POSE MANIPULATION AND RESET ====================
         */

         self.resetButtonElem = dojo.query("button.resetButton", element)[0];
         self.resetButton = new Button({
           label: "Reset",
           onClick: function() {
             if (self.webGLViewer) {
               self.webGLViewer.setupManipulator();
               self.webGLViewer.getManipulator().computeHomePosition();  
             }
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

        var activateDraggables = function(enable) {
          if (enable) {
            if (self.pitchRollHandler == undefined) {
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
              };
              self.pitchRollHandler.onMoving = function(mover) {
                var handlerImg = dojo.query(".pitchRollHandlerImg", mover.node)[0];
                var pitchLabel = dojo.query(".pitchLabel", mover.node)[0];
                var rollLabel = dojo.query(".rollLabel", mover.node)[0];
                var offset = moverRelativeTo(handlerImg, self.element);

                offset.x += 30;
                offset.y += 20;

                self.xyHandlerElem.style.zIndex = 1;
                self.yawZoomHandlerElem.style.zIndex = 1;
                self.pitchRollHandlerElem.style.zIndex = 2;

                self.pose.roll =  offset.x / self.pose.width - 0.5;
                self.pose.pitch = offset.y / self.pose.height - 0.5;
                self.pose.pitch *= -1;
                self.pose.roll *= 2 * 3.14159;
                self.pose.pitch *= 2 * 3.14159;
                self.pose.roll = Math.ceil((self.pose.roll) * 10) / 10;
                self.pose.pitch = Math.ceil((self.pose.pitch) * 10) / 10;
                pitchLabel.innerHTML = 'Pitch:' + self.pose.pitch;
                rollLabel.innerHTML =   'Roll:' + self.pose.roll;
              };

              self.yawZoomHandler = new Moveable(self.yawZoomHandlerElem);
              self.yawZoomHandler.onMoveStop = function(mover) {
                var handlerImg = dojo.query("img.yawZoomHandlerImg", mover.node)[0];
                var yawLabel = dojo.query("div.yawLabel", mover.node)[0];
                var zoomLabel = dojo.query("div.zoomLabel", mover.node)[0];
                yawLabel.innerHTML = '';
                zoomLabel.innerHTML = '';
                self.updateScene();
              };
              self.yawZoomHandler.onMoving = function(mover) {
                var handlerImg = dojo.query("img.yawZoomHandlerImg", mover.node)[0];
                var yawLabel = dojo.query("div.yawLabel", mover.node)[0];
                var zoomLabel = dojo.query("div.zoomLabel", mover.node)[0];
                var offset = moverRelativeTo(handlerImg, self.element);

                offset.x += 7;
                offset.y += 9;

                self.xyHandlerElem.style.zIndex = 1;
                self.yawZoomHandlerElem.style.zIndex = 2;
                self.pitchRollHandlerElem.style.zIndex = 1;

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
              };

              self.xyHandler = new Moveable(self.xyHandlerElem);
              self.xyHandler.onMoveStop = function(mover) {
                var handlerImg = dojo.query("img.xyHandlerImg", mover.node)[0];
                var xLabel = dojo.query("div.xLabel", mover.node)[0];
                var yLabel = dojo.query("div.yLabel", mover.node)[0];

                xLabel.innerHTML = '';
                yLabel.innerHTML = '';

                self.updateScene();
              };
              self.xyHandler.onMoving = function(mover) {
                var handlerImg = dojo.query("img.xyHandlerImg", mover.node)[0];
                var xLabel = dojo.query("div.xLabel", mover.node)[0];
                var yLabel = dojo.query("div.yLabel", mover.node)[0];
                var offset = moverRelativeTo(handlerImg, self.element);

                offset.x += 3;
                offset.y += 13;

                self.xyHandlerElem.style.zIndex = 2;
                self.yawZoomHandlerElem.style.zIndex = 1;
                self.pitchRollHandlerElem.style.zIndex = 1;

                self.pose.x = offset.x / self.pose.width - 0.5;
                self.pose.y = offset.y / self.pose.height - 0.5;
                self.pose.x *= 100;
                self.pose.y *= 100;
                self.pose.y = Math.ceil((self.pose.y) * 10) / 10;
                self.pose.x = Math.ceil((self.pose.x) * 10) / 10;
                xLabel.innerHTML = 'X:' + self.pose.x;
                yLabel.innerHTML = 'Y:' + self.pose.y;
              };
            }
            
            // show all draggables
            array.forEach(dojo.query(".draggable", element), function(entry, i) {
              entry.style.display = "inline";
            })
            
          } else {
            // show all draggables
            array.forEach(dojo.query(".draggable", element), function(entry, i) {
              entry.style.display = "none";
            })
          }
        }
        activateDraggables(self.enableDraggables);
        
        /**
         * === DRAG HANDLER ====================
         */
        var activateDND = function(enable) {
          if (enable) {
            self.createAvatar = function(item, mode) {
              if (mode == 'avatar') {
                 // create your avatar if you want
                 var avatar = dojo.create( 'div', { innerHTML: item.data });
                 var avatarPose = dojo.clone(self.pose);
                 avatarPose.width=60;
                 avatarPose.height=60;
                 var avatarImgUrl = urlSuffixForPose(avatarPose);
                 avatar.innerHTML = '<img src=' + self.imagePath + self.imageFormat + avatarImgUrl + ' /> ';
                 item.srcEcc = "VRMLViewer";
                 item.iconPoseUrl = self.imagePath + self.imageFormat + avatarImgUrl;
                 item.imagePath = self.imagePath;
                 item.imageFormat = self.imageFormat;
                 item.serverURL = self.serverURL;
                 item.pose = avatarPose;
                 return {node: avatar, data: item, type: item.type};
              }
              var handler = dojo.create( 'div', { innerHTML: '<img src="' + self.resRoot + 'img/drag.png" width="20px" />' });
              return {node: handler, data: item, type: item.type};
            };
      
            self.dndHandler = new Source(dojo.query("td.dndHandler", element)[0], {copyOnly: true, creator: self.createAvatar});
            self.dndHandler.insertNodes(false, [ { } ]);
            
            array.forEach(dojo.query(".dndHandler", element), function(entry, i) {
              entry.style.display = "inline";
            })
            
          } else {
            array.forEach(dojo.query(".dndHandler", element), function(entry, i) {
              entry.style.display = "none";
            })
            
          }
        }
        activateDND(self.enableDND);
        
        /**
         * === FILE NAVIGATION ====================
         */

        var activateListNavigation = function(enable) {
          if (enable) {
            array.forEach(dojo.query(".listNavigation", element), function(entry, i) {
              entry.style.display = "inline";
            });
          
            if (!self.fileListStore) {
              // setup fileStore
              self.fileListStore = new Observable(new Memory({
                data: [],
              }));
            
              self.prevButtonElem = dojo.query("button.prevButton", element)[0];
              self.nextButtonElem = dojo.query("button.nextButton", element)[0];
              self.fileListElem = dojo.query("div.fileList", element)[0];
            
              self.fileListSelect = new Selector({
                store: new ObjectStore({ objectStore: self.fileListStore }),
                onChange: function(name) {
                  var item = self.fileListStore.query({ id: name })[0];
                  self.imagePath = self.listDirectory + item.name;
                  self.updateScene();
                }
              }, self.fileListElem);
            
              self.prevButton = new Button({
                label: "<",
                onClick: function() {
                  var allItems = self.fileListStore.query();
                  var foundAt = 0;
                  for (var i = 0; i < allItems.total; i++) {
                    console.log(self.serverURL + self.imagePath + " === " + allItems[i].url);
                    if (self.serverURL + self.imagePath === allItems[i].url) {
                      foundAt = i;
                      break;
                    }
                  }
                
                  if (foundAt > 0) {
                    self.imagePath = self.listDirectory + allItems[foundAt - 1].name;
                    self.fileListSelect.attr( 'value', allItems[foundAt - 1].id );
                    if (self.serverURL + self.imagePath !== allItems[foundAt - 1].url)
                      console.log(self.serverURL + self.imagePath + " !== " + allItems[foundAt - 1].url);
                    self.updateScene();
                  }
                }
              }, self.prevButtonElem);

              self.nextButton = new Button({
                label: ">",
                onClick: function() {
                  var allItems = self.fileListStore.query();
                  var foundAt = 0;
                  for (var i = 0; i < allItems.total; i++) {
                    //console.log(self.serverURL + self.imagePath + " === " + allItems[i].url);
                    if (self.serverURL + self.imagePath === allItems[i].url) {
                      foundAt = i;
                      break
                    }
                  }
                  if (foundAt + 1 < allItems.total) {
                    self.imagePath = self.listDirectory + allItems[foundAt + 1].name + ".png";
                    self.fileListSelect.attr( 'value', allItems[foundAt + 1].id );
                    if (self.serverURL + self.imagePath !== allItems[foundAt + 1].url)
                      console.log(self.serverURL + self.imagePath + " !== " + allItems[foundAt + 1].url);
                    self.updateScene();
                  }
                }
              }, self.nextButtonElem);
            }
          } else {
            array.forEach(dojo.query(".listNavigation", element), function(entry, i) {
              entry.style.display = "none";
            });
          }
        }
        activateListNavigation(self.listNavigationStyle);
        
        var activateTreeNavigation = function(enable) {
          if (enable) {

            array.forEach(dojo.query(".treeNavigation", element), function(entry, i) {
              entry.style.display = "inline";
            });
          
            if (!self.fileTreeStore) {
              // setup fileStore
              self.fileTreeStore = new Observable(new Memory({
                data: [ { id: 'root', name:'3D Models'} ],
                getChildren: function(object){
                    return this.query({parent: object.id});
                }
              }));
          
              self.fileTreeModel = new ObjectStoreModel({
                  store: self.fileTreeStore,
                  query: { id: "root" }
              });

              // setup actual tree dijit
              self.fileTree = new dijit.Tree({
                  id: "fileTree" + self.instanceId,
                  model: self.fileTreeModel,
                  persist: false,
                  showRoot: false,
                  style: "height: 300px;",
                  onClick: function(item){
                    if ('url' in item) {
                      self.imagePath = item.url;
                      var newListDir = self.imagePath.substring(0, self.imagePath.lastIndexOf("/"));
                      if (newListDir.length > 0)
                        newListDir += '/';
                      if (newListDir !== self.listDirectory) {
                         self.listDirectory = newListDir;
                         self.refreshServer(self.serverURL, { skipTree: true });
                      }
                      self.updateScene();
                    }
                  },
                  getIconClass: function(item, opened) {
                      return (!item || !('url' in item)) ? (opened ? "dijitFolderOpened" : "dijitFolderClosed") : "dijitLeaf";
                  },
                  getIconStyle: function(item, opened){
                    if('url' in item) {
                      return { backgroundImage: "url('" + self.serverURL + item.url + self.imageFormat + "?width=16&height=16')"};
                    }
                  }
                  //return {backgroundImage: "url('" + item.url + "?width=16&height=16')"};
              });
          
              self.filesDropDownElem = dojo.query("td.filesDropDown", element)[0];

              self.serverBox = new TextBox({
                name: "Server",
                value: self.serverURL,
                style: "width: 65%",

                onKeyUp: function(e) {
                  if (self.browseButton) { 
                    if (this.get("value") !== self.serverURL) {
                      self.browseButton.setAttribute('label', 'Browse'); 
                    } else {
                      self.browseButton.setAttribute('label', 'Refresh'); 
                    }
                  }
                },

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

              self.filesDropDownContent = domConst.toDom('<div />');
              self.filesDropDownContent.appendChild(self.serverBox.domNode);
              self.filesDropDownContent.appendChild(self.browseButton.domNode);
              self.filesDropDownContent.appendChild(self.fileTree.domNode);

              self.filesToolTip = new TooltipDialog({ content:self.filesDropDownContent, style:"max-height:320px"});
              self.filesDropDown = new DropDownButton({ label: "Files", dropDown: self.filesToolTip });
              self.filesDropDownElem.appendChild(self.filesDropDown.domNode);

              self.fileStandby = new Standby({target: self.filesDropDownContent });
              self.filesDropDownContent.appendChild(self.fileStandby.domNode);
            }
          } else {
            array.forEach(dojo.query(".treeNavigation", element), function(entry, i) {
              entry.style.display = "none";
            });
          }
        }
        activateTreeNavigation(self.treeNavigationStyle);
        
        if (self.serverURL) {
          self.refreshServer(self.serverURL);
          self.updateScene();
        }
        /**
         * === MOVIE DROPDOWN ====================
         */
        
        if (self.enableMovies) {
          self.movieDropDownElem = dojo.query("div.movieDropDown", element)[0];
          self.movieAddButtonElem = dojo.query("button.movieAddButton", element)[0];

          self.movieDropDownContent = domConst.toDom(
            '<div style="overflow: auto; max-height: 420px;"> \
              <table><tr class="movieFormatLengthRow" /></tr><tr class="movieWidthHeightLengthRow" /></table> \
              <div class=\"dndArea\" /> \
            </div>'
          );
        
          self.movieFormatLengthRowElem = dojo.query("tr.movieFormatLengthRow", self.movieDropDownContent)[0];
          self.movieWidthHeightLengthRowElem = dojo.query("tr.movieWidthHeightLengthRow", self.movieDropDownContent)[0];
          self.movieDnDArea = dojo.query("div.dndArea", self.movieDropDownContent)[0];
        
          self.createMovieThumb = function(item, mode) {
            if (mode == 'avatar') {
               // when dragged 
               var avatar = dojo.create( 'div', { innerHTML: item.data });
               var avatarPose = dojo.clone(self.pose);
               avatarPose.width = 60;
               avatarPose.height = 60;
               var avatarImgUrl = urlSuffixForPose(avatarPose);
               avatar.innerHTML = '<img src=' + self.imagePath + avatarImgUrl + ' /> ';
               item.srcEcc = "VRMLViewer";
               item.iconPoseUrl = self.imagePath + avatarImgUrl;
               item.imagePath = self.imagePath;
               item.serverURL = self.serverURL;
               item.pose = avatarPose;
               return {node: avatar, data: item, type: item.type};
            } else {
            
              // when added to list
              var thumb = domConst.toDom("\
                <div>\
                  <table><tr><td>\
                    <img class=\"movieThumb\"/>\
                    <img class=\"removeThumb\" style=\"vertical-align: top; margin: -3px 0px 0px -8px; width: 20px; height: 20px;\"/>\
                  </td><td align=\"left\">\
                    <table><tr>\
                      <td>Frame:</td><td><div class=\"relFrameLength\"/></td>\
                      <td><div class=\"fillInSeries\" \></td>\
                    </tr><tr>\
                      <td>Transition:</td><td><div class=\"relTransitionLength\"/></td>\
                    </tr></table>\
                  </td></tr></table>\
                </div>\
              ");
              thumb = dojo.query("div", thumb)[0];
            
              var thumbImgElem = dojo.query("img.movieThumb", thumb)[0];
              var removeImgElem = dojo.query("img.removeThumb", thumb)[0];
              var relFrameLengthElem = dojo.query("div.relFrameLength", thumb)[0];
              var relTransitionLengthElem = dojo.query("div.relTransitionLength", thumb)[0];
              var fillInSeriesElem = dojo.query("div.fillInSeries", thumb)[0];
            
              item.getThisAndNeighborsFromDnD = function() {
                var thisAndNeighbors = {};
                self.addToMovieHandler.forInItems(function(obj, key, ctx) {
                  if (obj.data === item) {
                    thisAndNeighbors.this = { key: key, obj: obj };
                  } else {
                    thisAndNeighbors.before = { key: key, obj: obj };
                  }
                  if (thisAndNeighbors.this) {
                    thisAndNeighbors.after = { key: key, obj: obj };
                    return thisAndNeighbors;
                  }
                });
                return thisAndNeighbors;
              };
            
              item.relFrameLengthSlider = new HorizontalSlider({ 
                value: 50,
                title: "Relative Duration of Frame",
                style: "width:150px;"
              }, relFrameLengthElem);

              item.relTransitionLengthSlider = new HorizontalSlider({ 
                value: 100,
                title: "Relative Duration of Transition",
                style: "width:150px;"
              }, relTransitionLengthElem);
            
              removeImgElem.onclick = function() {
                var thisItem = item.getThisAndNeighborsFromDnD();
                if (thisItem.this) {
                  // haha - what a mess!
                  self.addToMovieHandler.selectNone();
                  self.addToMovieHandler.selection[thisItem.this.key] = thisItem.this.obj;
                  self.addToMovieHandler.deleteSelectedNodes();
                }
                // disable create button if this was the last one
                if (!thisItem.after || !thisItem.before) {
                  self.movieCreateButton.setAttribute('disabled', true);
                }
              }
            
              item.fillInSeriesButton = new Button({ 
                label: "Insert Series",
                style: "display: none;",
                onClick: function(){
                  alert("foo");
                }
              }, fillInSeriesElem);
            
              removeImgElem.src = self.resRoot + "img/close.png";
            
              var thumbPose = dojo.clone(self.pose);
              thumbPose.width = self.pose.width / 10;
              thumbPose.height = self.pose.height / 10;
              var thumbImgUrl = urlSuffixForPose(thumbPose);
            
              thumbImgElem.src = self.imagePath + thumbImgUrl;
              // removeImgElem.src = self.resRoot + 'img/close.png';
                        
              item.srcEcc = "VRMLViewer";
              item.iconPoseUrl = self.imagePath + thumbImgUrl;
              item.imagePath = self.imagePath;
              item.serverURL = self.serverURL;
              item.pose = thumbPose;
            
              return {node: thumb, data: item, type: item.type};
            }
          };

          self.addToMovieHandler = new Source(self.movieDnDArea, {copyOnly: true, creator: self.createMovieThumb});

          self.movieFormatSelection = new Selector({
            name: "movieFormat",
            style: "width: 320px",
            options: []
          });
          self.populateMovieCodecs("http://" + self.serverURL + '/movie/codecs', self.movieFormatSelection);

          self.movieFormatLengthRowElem.appendChild(dojo.create('td', { innerHTML: 'Format:'} ));
          self.movieFormatLengthRowElem.appendChild(dojo.create('td', { colspan: "2"}));
          self.movieFormatLengthRowElem.lastChild.appendChild(self.movieFormatSelection.domNode);
        
          self.movieHeightSpinner = new NumberSpinner({
            value: 400,
            smallDelta: 1,
            style: "width: 60px",
            constraints: { min:40, places:0 },
          });
        
          self.movieWidthSpinner = new NumberSpinner({
            value: 600,
            smallDelta: 1,
            style: "width: 60px",
            constraints: { min:40, places:0 },
          });

          self.movieCreateButton = new Button({
            label: "Create",
            disabled: true,
            onClick: function(){
                        
              var form = document.createElement("form");

              form.setAttribute("method", "post");
              form.setAttribute("action", self.serverURL + "/movie");

              var submitData = {};
              submitData.frames = [];
              submitData.movieLength = self.movieDurationSpinner.value;
              submitData.format = self.movieFormatSelection.value;
              submitData.width = self.movieWidthSpinner.value;
              submitData.height = self.movieHeightSpinner.value;
            
              self.addToMovieHandler.forInItems(function(obj, key, ctx) {
                var jsonData = {
                  iconPoseUrl: obj.data.iconPoseUrl,
                  imagePath: obj.data.imagePath,
                  serverURL: obj.data.serverURL,
                  pose: obj.data.pose,
                  relFrameLength: obj.data.relFrameLengthSlider.value,
                  relTransitionLength: obj.data.relTransitionLengthSlider.value,
                }
                submitData.frames.push(jsonData);
              });

              var hiddenField = document.createElement("input");
              hiddenField.setAttribute("type", "hidden");
              hiddenField.setAttribute("name", "data");
              hiddenField.setAttribute("value", JSON.stringify(submitData));

              form.appendChild(hiddenField);
            
              // this will not save the returned binary file
              // self.xhr.post({
              //   form: form,
              //   load: function(data){
              //     alert("asd");
              //   }
              // });
            
              document.body.appendChild(form);
              form.submit();
              document.body.removeChild(form);
            }
          });

          self.movieDurationSpinner = new NumberSpinner({
            value: 10,
            smallDelta: 1,
            style: "width: 40px",
            constraints: { min:0, places:0 },
          });

          // append format duration cell
          self.movieWidthHeightLengthRowElem.appendChild(dojo.create('td', { innerHTML: 'Size:'} ));
          var movieDimensionCell = dojo.create('td');
          movieDimensionCell.appendChild(self.movieWidthSpinner.domNode);
          movieDimensionCell.appendChild(dojo.create('span', { innerHTML: "x"} ));
          movieDimensionCell.appendChild(self.movieHeightSpinner.domNode);
          movieDimensionCell.appendChild(self.movieDurationSpinner.domNode);
          movieDimensionCell.appendChild(dojo.create('span', { innerHTML: "sec"} ));        
          self.movieWidthHeightLengthRowElem.appendChild(movieDimensionCell);

          self.movieWidthHeightLengthRowElem.appendChild(dojo.create('td', { align: "right"}));
          self.movieWidthHeightLengthRowElem.lastChild.appendChild(self.movieCreateButton.domNode);


          self.movieToolTip = new TooltipDialog({ content:self.movieDropDownContent });
          self.movieDropDown = new DropDownButton({ 
            label: "Movie", 
            style: "display: none;",
            dropDown: self.movieToolTip });
          self.movieDropDownElem.appendChild(self.movieDropDown.domNode);

          self.movieAddButton = new Button({
            label: "+",
            style: "margin-left: -10px; display: none;",
            onClick: function(){
              if (self.movieFormatSelection.options.length == 0) {
                self.populateMovieCodecs(self.serverURL + '/movie/codecs', self.movieFormatSelection);
              }
              // we could pass item.data here to creator
              self.addToMovieHandler.insertNodes(false, [ { } ]);
              self.movieCreateButton.setAttribute('disabled', false);
            
            }
          }, self.movieAddButtonElem);
        } else {
          // remove movie controls
          var movieControls = dojo.query("td.movieControls", element)[0];
          movieControls.parentNode.removeChild(movieControls);
        }

        // do we have parameters for the initial pose?
        if(self.params && self.params.pose)
          self.setPose(self.params.imagePath, self.params.pose, self.params.serverURL);

      });
    });


}
