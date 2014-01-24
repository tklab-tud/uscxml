function Miles(element, params) {
  // private attributes
  var self = this;
  
  // private instanceId
  if (!Miles.instances)
    Miles.instances = 0;
  this.instanceId = Miles.instances++;
    
  // public attributes defaults
  this.imageIteration = 0;
  this.resRoot = "";
  this.reflectorIp = "88.131.107.12";
  this.email       = "user@smartvortex.eu";
  this.problemName = "webconfero";
  this.remoteEmail = "other@smartvortex.eu";
  this.scxmlURL    = "localhost:8080"

  this.width = 320;
  this.height = 240;

  this.showVideo = true;
  this.enableAudio = true;
  this.activateCamera = true;
  this.openMicrophone = true;
  this.videoFramerate = 25;
  this.videoHeight = this.height;
  this.videoWidth = this.width;

  // copy over values from constructor arguments
  if (params) {
    for (var param in params) {
      if (self.hasOwnProperty(param))
        self[param] = params[param];
    }
  }

  // private attributes
  var connected = false;

  var participants = []; // empty array
  var videoCompressions = [
    { value: 'jpeg', label: "JPEG" },
    { value: 'h263', label: "H.263" },
    { value: 'h264', label: "H.264" },
  ];
  var videoCompression = "";

  var audioEncodings = [
    { value: 'pcm', label: "PCM" },
    { value: 'ulaw', label: "uLaw" },
    { value: 'ogg', label: "Ogg Theora" },
  ];
  var audioEncoding = "";
  
  var repollInterval = {
    image: 20,
    chat: 500,
    participants: 1000
  };
  
  var surpressPublication = false; // do not publish changes performed from subscriptions
  var stopChatScrolling = false;
    
  // called when dojo loaded all requirements below
  this.connect = function() {
    var query = "";
    query += "?reflector=" + encodeURIComponent(self.reflectorIp);
    query += "&userid=" + encodeURIComponent(self.email);
    query += "&session=" + encodeURIComponent(self.problemName);
    
    //self.messageElem.innerHTML += "Connecting to http://" + self.scxmlURL + "/miles/start" + query + "<br />";
    self.xhr.get({
      // The URL to request
      url: "http://" + self.scxmlURL + "/miles/start" + query,
      // handleAs:"text",
      error: function(err) {
        console.log(err);
      },
      load: function(result) {
        connected = true;
        // toggle connect button to disconnect
        self.connectDropDown.dropDown.onCancel(true);
        self.controlElem.replaceChild(self.controlDropDown.domNode, self.connectDropDown.domNode);

        showChat();
        
        // trigger continuous updates
        refreshImage();
        getChatText();
        getParticipants();
      }
    });  
  }

  this.disconnect = function() {
    var query = "";
    query += "?reflector=" + encodeURIComponent(self.reflectorIp);
    query += "&userid=" + encodeURIComponent(self.email);
    query += "&session=" + encodeURIComponent(self.problemName);
    
    self.xhr.get({
      // The URL to request
      url: "http://" + self.scxmlURL + "/miles/stop" + query,
      // handleAs:"text",
      error: function(err) {
        console.log(err);
      },
      load: function(result) {
        connected = false;
        hideChat();
        self.controlDropDown.dropDown.onCancel(true);
        self.controlElem.replaceChild(self.connectDropDown.domNode, self.controlDropDown.domNode);
      }
    });  
  }
  
  var hideChat = function() {
    // hide chat elements until connected
    for(var key in self.chatElems) {
      if (self.chatElems.hasOwnProperty(key) && "style" in self.chatElems[key])
        self.chatElems[key].style.display = "none";
    }
  }
  
  var showChat = function() {
    for(var key in self.chatElems) {
      if (self.chatElems.hasOwnProperty(key) && "style" in self.chatElems[key])
        self.chatElems[key].style.display = "";
    }
  }
  
  var getParticipants = function() {
    if (!connected)
      return;

    var query = "";
    self.xhr.get({
      // The URL to request
      url: "http://" + self.scxmlURL + "/miles/participants" + query,
      handleAs:"json",
      error: function(err) {
        console.log(err);
        setTimeout(getParticipants, repollInterval.participants);
      },
      load: function(result) {
        if (result.participants) {
          participants = result.participants;
        }
        setTimeout(getParticipants, repollInterval.participants);
      }
    });
  }
  
  // fetch a base64 encoded image and set it as the src attribute
  var refreshImage = function() {
    if (!connected)
      return;

    var query = "";
    query += "?userid=" + encodeURIComponent(self.remoteEmail);
    self.xhr.get({
      // The URL to request
      url: "http://" + self.scxmlURL + "/miles/thumbnail" + query,
      handleAs:"text",
      headers:{
        "X-Content-Encoding": "base64"
      },
      error: function(err) {
        console.log(err);
        setTimeout(refreshImage, repollInterval.image);
      },
      load: function(result) {
        self.pictureElem.src = "data:image/jpeg;base64," + result;
        //self.messageElem.innerHTML = self.imageIteration++;
        setTimeout(refreshImage, repollInterval.image);
      }
    });  
  };

  var getChatText = function() {
    if (!connected)
      return;

    self.xhr.get({
      // The URL to request
      url: "http://" + self.scxmlURL + "/miles/gettext",
      handleAs:"json",
      error: function(err) {
        console.log(err);
        setTimeout(getChatText, repollInterval.chat);
      },
      load: function(result) {
        if (result.message) {
          self.chatOutputElem.innerHTML += result.message + '<br />';
          if (!stopChatScrolling)
            self.chatOutputElem.scrollTop = self.chatOutputElem.scrollHeight;
        }
        setTimeout(getChatText, repollInterval.chat);
      }
    });  
  };


  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom",
           "dojo/on",
           "dojo/topic",
           "dojo/_base/unload",
           "dijit/form/DropDownButton",
           "dijit/TooltipDialog",
           "dijit/form/TextBox",
           "dijit/form/Button",
           "dijit/form/CheckBox",
           "dijit/form/Select",
           "dijit/form/NumberSpinner",
           "dojo/ready"], 
    function(domConst, 
             xhr, 
             dom,
             on,
             topic,
             baseUnload,
             DropDownButton,
             TooltipDialog,
             TextBox,
             Button,
             CheckBox,
             Select,
             NumberSpinner,
             ready) {      
      ready(function() {
        self.xhr = xhr;
        
        // if we were passed an id, resolve to dom node
        if (typeof(element) === 'string') {
          element = dom.byId(element);
        }
        element.style.width = self.width + "px";

        baseUnload.addOnWindowUnload(function(){
         self.disconnect();
        });

        // dynamically assemble the DOM we need
        element.appendChild(domConst.toDom('\
          <table>\
            <tr>\
              <td valign="top" colspan="2" >\
                  <div style="position: relative; padding: 0px">\
                    <img class="picture" src="' + self.resRoot + 'emptyface.jpg"></img>\
                    <div style="position: absolute; left: 10px; top: 10px">\
                      <table></tr>\
                        <td class="control" style="vertical-align: middle"></td>\
                      </tr></table>\
                    </div>\
                  </div>\
              </td>\
            </tr>\
            <tr><td valign="top" colspan="2" >\
                  <div class="chatOutput" style="max-height:120px; overflow: auto">\
            </td></tr>\
            <tr class="chat">\
              <td valign="top" style="vertical-align: middle">\
                <div class="chatInput">\
              </td>\
              <td valign="top"><div class="chatSendButton"></td>\
            </tr>\
            <tr>\
              <td valign="top" colspan="2" >\
                  <div class="messages">\
              </td>\
            </tr>\
          </table>\
        '));
        
        // from the above DOM, fetch some nodes to put dojo widgets in
        self.pictureElem = dojo.query("img.picture", element)[0];
        self.pictureElem.width = self.width;
        self.pictureElem.height = self.height;
        self.controlElem = dojo.query("td.control", element)[0];
        self.messageElem = dojo.query("div.messages", element)[0];
        self.chatOutputElem = dojo.query("div.chatOutput", element)[0];
        self.chatOutputElem.style.fontSize = "0.8em";
        self.chatElems = dojo.query(".chat", element);

        console.log(self.controlElem);

        hideChat();
        
        on(self.chatOutputElem, "mouseover", function(evt) {
          stopChatScrolling = true;
        });
        on(self.chatOutputElem, "mouseout", function(evt) {
          stopChatScrolling = false;          
        });
        
        self.chatInputElem = dojo.query("div.chatInput", element)[0];
        
        self.chatSendButton = new Button({
          label: "Send",
          onClick: function(){
            self.xhr.post({
              // The URL to request
              url: "http://" + self.scxmlURL + "/miles/text",
              contentType: 'application/json',
              postData: dojo.toJson({
                message: self.chatInput.get('value'),
                userid: self.email
              }),
              error: function(err) {
                console.log(err);
              },
              load: function(result) {
                self.chatInput.set('value', '');
              }
            });  
            
          }
          
        }, dojo.query("div.chatSendButton", element)[0]);
        
        // the chat interface
        self.chatInput = new TextBox({
          name: "chatInput",
          style: "width: 100%",
          onKeyDown: function(e) {
            var code = e.keyCode || e.which;
            if( code === 13 ) {
              e.preventDefault();
              self.chatInput.get('value'); // send button reads empty string otherwise?!
              self.chatSendButton.onClick();
              return false; 
            }
          },
        }, self.chatInputElem);
        
        
        // the connect dropdown button
        self.connectDropDownContent = domConst.toDom('\
          <div>\
            <table>\
              <tr><td>Problem Name:</td><td><div class="problemName" /></td></tr>\
              <tr><td>Your Email:</td><td><div class="email" /></td></tr>\
              <tr><td>Other Email:</td><td><div class="remoteEmail" /></td></tr>\
              <tr><td>Reflector Host:</td><td><div class="reflectorIp" /></td></tr>\
              <tr><td>Video Server:</td><td><div class="scxmlURL" /></td></tr>\
              <tr><td></td><td align="right"><div class="connectButton" /></td></tr>\
          </div>\
        ');
        self.connectToolTip = new TooltipDialog({ content:self.connectDropDownContent, style:"max-height:320px"});
        self.connectDropDown = new DropDownButton({ label: "Connect", dropDown: self.connectToolTip });
        
        // Connect parameters
        self.problemNameBox = new TextBox({
          name: "problemName",
          value: self.problemName,
          style: "width: 100%",
          onChange: function(){
            self.problemName = self.problemNameBox.get('value');
          }
          
        });
        dojo.query("div.problemName", self.connectToolTip.domNode)[0].appendChild(self.problemNameBox.domNode);

        self.emailBox = new TextBox({
          name: "email",
          value: self.email,
          style: "width: 100%",
          onChange: function(){
            self.email = self.emailBox.get('value');
          }
        });
        dojo.query("div.email", self.connectToolTip.domNode)[0].appendChild(self.emailBox.domNode);

        self.remoteEmailBox = new TextBox({
          name: "remoteEmail",
          value: self.remoteEmail,
          style: "width: 100%",
          onChange: function(){
            self.remoteEmail = self.remoteEmailBox.get('value');
          }
        });
        dojo.query("div.remoteEmail", self.connectToolTip.domNode)[0].appendChild(self.remoteEmailBox.domNode);

        self.reflectorIpBox = new TextBox({
          name: "self.reflectorIp",
          value: self.reflectorIp,
          style: "width: 100%",
          onChange: function(){
            self.reflectorIp = self.reflectorIpBox.get('value');
          }
        });
        dojo.query("div.reflectorIp", self.connectToolTip.domNode)[0].appendChild(self.reflectorIpBox.domNode);

        self.scxmlURLBox = new TextBox({
          name: "scxmlURL",
          value: self.scxmlURL,
          style: "width: 100%",
          onChange: function(){
            self.scxmlURL = self.scxmlURLBox.get('value');
          }
        });
        dojo.query("div.scxmlURL", self.connectToolTip.domNode)[0].appendChild(self.scxmlURLBox.domNode);

        self.connectButton = new Button({
          label: "Connect",
          onClick: function(){
            self.connect();
          }
        });
        dojo.query("div.connectButton", self.connectToolTip.domNode)[0].appendChild(self.connectButton.domNode);

        // Control parameters
        self.controlDropDownContent = domConst.toDom('\
          <div>\
            <fieldset name="global">\
              <legend>Global Options</legend>\
              <table>\
                <tr><td>Activate Camera:</td><td><div class="activateCamera" /></td></tr>\
                <tr><td style="padding-left: 1em">Compression:</td><td><div class="videoCompression" /></td></tr>\
                <tr><td style="padding-left: 1em">Framerate:</td><td><div class="videoFramerate" /></td></tr>\
                <tr><td style="padding-left: 1em">Width:</td><td><div class="videoWidth" /></td></tr>\
                <tr><td style="padding-left: 1em">Height:</td><td><div class="videoHeight" /></td></tr>\
                <tr><td>Open Microphone:</td><td><div class="openMicrophone" /></td></tr>\
                <tr><td style="padding-left: 1em">Encoding:</td><td><div class="audioEncoding" /></td></tr>\
              </table>\
            </fieldset>\
            <fieldset name="session">\
              <legend>Session Options</legend>\
              <table>\
                <tr><td>Enable Audio:</td><td><div class="enableAudio" /></td></tr>\
                <tr><td>Show Video:</td><td><div class="showVideo" /></td></tr>\
                <tr><td></td><td align="right"><div class="disconnectButton" /></td></tr>\
              </table>\
            </fieldset>\
          </div>\
        ');
        self.controlToolTip = new TooltipDialog({ content:self.controlDropDownContent, style:"max-height:320px"});
        self.controlDropDown = new DropDownButton({ label: "Session", dropDown: self.controlToolTip });
        
        // Control parameters
        
        // global camera
        topic.subscribe("miles/activateCamera", function(data) {
          surpressPublication = true;
          self.activateCameraCheckbox.set('value', data.activateCamera);
          self.videoCompressionSelect.set('value', data.videoCompression);
          self.videoFramerateSpinner.set('value', data.videoFramerate);
          self.videoWidthSpinner.set('value', data.videoWidth);
          self.videoHeightSpinner.set('value', data.videoHeight);
          surpressPublication = false;
        });

        var publishCameraParameters = function() {
          topic.publish("miles/activateCamera", {
            "activateCamera": self.activateCamera,
            "videoCompression": self.videoCompression,
            "videoFramerate": self.videoFramerate,
            "videoWidth": self.videoWidth,
            "videoHeight": self.videoHeight
          });
          // tell the server
          if (activateCamera) {
            var query = "";
            query += "?width=" + encodeURIComponent(self.videoWidth);
            query += "&height=" + encodeURIComponent(self.videoHeight);
            query += "&framerate=" + encodeURIComponent(self.videoFramerate);
            query += "&compression=" + encodeURIComponent(self.videoCompression);
            self.xhr.get({
              url: "http://" + self.scxmlURL + "/miles/sendvideo" + query,
              error: function(err) {
                console.log(err);
              }
            });  
          } else {
            self.xhr.get({
              url: "http://" + self.scxmlURL + "/miles/sendvideooff",
              error: function(err) {
                console.log(err);
              }
            });  
          }
        };

        self.activateCameraCheckbox = new CheckBox({
          name: "activateCamera",
          checked: self.activateCamera,
          onChange: function() { 
            self.activateCamera = self.activateCameraCheckbox.get('value');
            if (!surpressPublication)
              publishCameraParameters();
          }
        });
        dojo.query("div.activateCamera", self.controlToolTip.domNode)[0].appendChild(self.activateCameraCheckbox.domNode);
        
        self.videoCompressionSelect = new Select({
          name: "videoCompression",
          options: self.videoCompressions,
          onChange: function() { 
            self.videoCompression = self.videoCompressionSelect.get('value');
            if (!surpressPublication)
              publishCameraParameters();
          }
        });
        dojo.query("div.videoCompression", self.controlToolTip.domNode)[0].appendChild(self.videoCompressionSelect.domNode);

        self.videoFramerateSpinner = new NumberSpinner({
          name: "videoFramerate",
          value: self.videoFramerate,
          style: "width: 50px",
          onChange: function() { 
            self.videoFramerate = self.videoFramerateSpinner.get('value');
            if (!surpressPublication)
              publishCameraParameters();
          }
        });
        dojo.query("div.videoFramerate", self.controlToolTip.domNode)[0].appendChild(self.videoFramerateSpinner.domNode);

        self.videoWidthSpinner = new NumberSpinner({
          name: "videoWidth",
          value: self.videoWidth,
          style: "width: 50px",
          onChange: function() { 
            self.videoWidth = self.videoWidthSpinner.get('value');
            if (!surpressPublication)
              publishCameraParameters();
          }
        });
        dojo.query("div.videoWidth", self.controlToolTip.domNode)[0].appendChild(self.videoWidthSpinner.domNode);

        self.videoHeightSpinner = new NumberSpinner({
          name: "videoHeight",
          value: self.videoHeight,
          style: "width: 50px",
          onChange: function() { 
            self.videoHeight = self.videoHeightSpinner.get('value');
            if (!surpressPublication)
              publishCameraParameters();
          }
        });
        dojo.query("div.videoHeight", self.controlToolTip.domNode)[0].appendChild(self.videoHeightSpinner.domNode);

        // global microphone
        topic.subscribe("miles/openMicrophone", function(data) {
          surpressPublication = true;
          self.openMicrophoneCheckbox.set('value', data.openMicrophone);
          self.audioEncodingSelect.set('value', data.audioEncoding);
          surpressPublication = false;
        });

        var publishMicrophoneParameters = function() {
          topic.publish("miles/openMicrophone", {
            "openMicrophone": openMicrophone,
            "audioEncoding": audioEncoding
          });
          // tell the server
          if (openMicrophone) {
            var query = "";
            query += "?encoding=" + encodeURIComponent(self.audioEncoding);
            self.xhr.get({
              url: "http://" + self.scxmlURL + "/miles/sendaudio" + query,
              error: function(err) {
                console.log(err);
              }
            });  
          } else {
            self.xhr.get({
              url: "http://" + self.scxmlURL + "/miles/sendaudiooff",
              error: function(err) {
                console.log(err);
              }
            });  
          }
        }

        self.openMicrophoneCheckbox = new CheckBox({
          name: "openMicrophone",
          value: self.openMicrophone,
          checked: self.openMicrophone,
          onChange: function() { 
            self.openMicrophone = self.openMicrophoneCheckbox.get('value');
            if (!surpressPublication)
              publishMicrophoneParameters();
          }
        });
        dojo.query("div.openMicrophone", self.controlToolTip.domNode)[0].appendChild(self.openMicrophoneCheckbox.domNode);
        
        self.audioEncodingSelect = new Select({
          name: "audioEncoding",
          options: self.audioEncodings,
          onChange: function() {
            self.audioEncoding = self.audioEncodingSelect.get('value');
            if (!surpressPublication)
              publishMicrophoneParameters();
          }
        });
        dojo.query("div.audioEncoding", self.controlToolTip.domNode)[0].appendChild(self.audioEncodingSelect.domNode);


        // session scoped parameters
        self.enableAudioCheckbox = new CheckBox({
          name: "enableAudio",
          value: self.enableAudio,
          checked: self.enableAudio,
        });
        dojo.query("div.enableAudio", self.controlToolTip.domNode)[0].appendChild(self.enableAudioCheckbox.domNode);

        self.showVideo = new CheckBox({
          name: "showVideo",
          value: self.showVideo,
          checked: self.showVideo,
        });
        dojo.query("div.showVideo", self.controlToolTip.domNode)[0].appendChild(self.showVideo.domNode);

        self.disconnectButton = new Button({
          label: "Disconnect",
          onClick: function(){
            self.disconnect();
          }
        });
        dojo.query("div.disconnectButton", self.controlToolTip.domNode)[0].appendChild(self.disconnectButton.domNode);

        // intially append the connect dropdown
        self.controlElem.appendChild(self.connectDropDown.domNode);
        
      })
  });
}
