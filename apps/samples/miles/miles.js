function Miles(element, params) {
  // private attributes
  var self = this;
  
  // private instanceId
  if (!Miles.instances)
    Miles.instances = 0;
    
  // public attributes
  this.instanceId = Miles.instances++;
  this.element = element;
  this.connected = false;
  this.imageIteration = 0;

  this.width = 300;
  this.height = 200;

  // private attributes
  var scxmlURL    = "localhost:8080"
  var reflectorIp = "88.131.107.12"
  var email       = "user@smartvortex.eu";
  var problemName = "webconfero";
  var remoteEmail = "other@smartvortex.eu";

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
    image: 50,
    chat: 500,
    participants: 1000
  };
  
  var showVideo = true;
  var enableAudio = true;
  var stopChatScrolling = false;
  var activateCamera = true;
  var openMicrophone = true;
  var videoFramerate = 25;
  var videoHeight = self.height;
  var videoWidth = self.width;
  
  // override with parameters if given
  this.params = params;
  if (params && params.scxmlURL)     scxmlURL = params.scxmlURL;
  if (params && params.reflectorIp)  reflectorIp = params.reflectorIp;
  if (params && params.email)        email = params.email;
  if (params && params.problemName)  problemName = params.problemName;

  // called when dojo loaded all requirements below
  this.connect = function() {
    var query = "";
    query += "?reflector=" + encodeURIComponent(reflectorIp);
    query += "&userid=" + encodeURIComponent(email);
    query += "&session=" + encodeURIComponent(problemName);
    
    self.xhr.get({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/start" + query,
      // handleAs:"text",
      error: function(err) {
        console.log(err);
      },
      load: function(result) {
        self.connected = true;

        // toggle connect button to disconnect
        self.connectDropDown.dropDown.onCancel(true);
        self.controlElem.replaceChild(self.controlDropDown.domNode, self.connectDropDown.domNode);
        
        // trigger continuous updates
        refreshImage();
        getChatText();
        getParticipants();
      }
    });  
  }

  this.disconnect = function() {
    self.connected = false;
    self.controlDropDown.dropDown.onCancel(true);
    self.controlElem.replaceChild(self.connectDropDown.domNode, self.controlDropDown.domNode);
  }
  
  var getParticipants = function() {
    var query = "";
    self.xhr.get({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/participants" + query,
      handleAs:"json",
      error: function(err) {
        console.log(err);
        if (self.connected) {
          setTimeout(getParticipants, repollInterval.participants);
        }
      },
      load: function(result) {
        if (result.participants) {
          participants = result.participants;
        }
        if (self.connected) {
          console.log(participants);
          setTimeout(getParticipants, repollInterval.participants);
        }
      }
    });
  }
  
  // fetch a base64 encoded image and set it as the src attribute
  var refreshImage = function() {
    var query = "";
    query += "?userid=" + encodeURIComponent(email);
    self.xhr.get({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/thumbnail" + query,
      handleAs:"text",
      headers:{
        "X-Content-Encoding": "base64"
      },
      error: function(err) {
        console.log(err);
        if (self.connected) {
          setTimeout(refreshImage, repollInterval.image);
        }
      },
      load: function(result) {
        self.pictureElem.src = "data:image/jpeg;base64," + result;
        if (self.connected) {
          self.messageElem.innerHTML = self.imageIteration++;
          setTimeout(refreshImage, repollInterval.image);
        }
      }
    });  
  };

  var getChatText = function() {
    self.xhr.get({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/gettext",
      handleAs:"json",
      error: function(err) {
        console.log(err);
        if (self.connected) {
          setTimeout(getChatText, repollInterval.chat);
        } 
      },
      load: function(result) {
        if (result.message) {
          self.chatOutputElem.innerHTML += stopChatScrolling + " " + Math.random() + ": " + result.message + '<br />';
          if (!stopChatScrolling)
            self.chatOutputElem.scrollTop = self.chatOutputElem.scrollHeight;
        }
        if (self.connected) {
          setTimeout(getChatText, repollInterval.chat);
        }
      }
    });  
  };


  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom",
           "dojo/on",
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
//          alert("unloading...");
        });

        // dynamically assemble the DOM we need
        element.appendChild(domConst.toDom('\
          <table>\
            <tr>\
              <td valign="top" colspan="2" >\
                  <div style="position: relative; padding: 0px">\
                    <img class="picture" src="emptyface.jpg"></img>\
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
            <tr>\
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
              url: "http://" + scxmlURL + "/miles/chat",
              contentType: 'text/plain',
              postData: dojo.toJson({
                message: chatInputElem.value
              }),
              error: function(err) {
                console.log(err);
              },
              load: function(result) {}
            });  
            
          }
        }, dojo.query("div.chatSendButton", element)[0]);
        
        // the chat interface
        self.chatInput = new TextBox({
          name: "chatInput",
          style: "width: 100%",
        }, self.chatInputElem);
        
        
        // the connect dropdown button
        self.connectDropDownContent = domConst.toDom('\
          <div>\
            <table>\
              <tr><td>Problem Name:</td><td><div class="problemName" /></td></tr>\
              <tr><td>Your Email:</td><td><div class="email" /></td></tr>\
              <!-- tr><td>Other Email:</td><td><div class="remoteEmail" /></td></tr -->\
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
          value: problemName,
          style: "width: 100%",
        });
        dojo.query("div.problemName", self.connectToolTip.domNode)[0].appendChild(self.problemNameBox.domNode);

        self.emailBox = new TextBox({
          name: "email",
          value: email,
          style: "width: 100%",
        });
        dojo.query("div.email", self.connectToolTip.domNode)[0].appendChild(self.emailBox.domNode);

        // self.remoteEmailBox = new TextBox({
        //   name: "remoteEmail",
        //   value: remoteEmail,
        //   style: "width: 100%",
        // });
        // dojo.query("div.remoteEmail", self.connectToolTip.domNode)[0].appendChild(self.remoteEmailBox.domNode);

        self.reflectorIpBox = new TextBox({
          name: "reflectorIp",
          value: reflectorIp,
          style: "width: 100%",
        });
        dojo.query("div.reflectorIp", self.connectToolTip.domNode)[0].appendChild(self.reflectorIpBox.domNode);

        self.scxmlURLBox = new TextBox({
          name: "scxmlURL",
          value: scxmlURL,
          style: "width: 100%",
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
            <table>\
              <tr><td>Activate Camera:</td><td><div class="activateCamera" /></td></tr>\
              <tr><td style="padding-left: 1em">Compression:</td><td><div class="videoCompression" /></td></tr>\
              <tr><td style="padding-left: 1em">Framerate:</td><td><div class="videoFramerate" /></td></tr>\
              <tr><td style="padding-left: 1em">Width:</td><td><div class="videoWidth" /></td></tr>\
              <tr><td style="padding-left: 1em">Height:</td><td><div class="videoHeight" /></td></tr>\
              <tr><td>Open Microphone:</td><td><div class="openMicrophone" /></td></tr>\
              <tr><td style="padding-left: 1em">Encoding:</td><td><div class="audioEncoding" /></td></tr>\
              <tr><td colspan="2"><hr /></td></tr>\
              <tr><td>Enable Audio:</td><td><div class="enableAudio" /></td></tr>\
              <tr><td>Show Video:</td><td><div class="showVideo" /></td></tr>\
              <tr><td colspan="2"><hr /></td></tr>\
              <tr><td></td><td align="right"><div class="disconnectButton" /></td></tr>\
          </div>\
        ');
        self.controlToolTip = new TooltipDialog({ content:self.controlDropDownContent, style:"max-height:320px"});
        self.controlDropDown = new DropDownButton({ label: "Session", dropDown: self.controlToolTip });
        
        // Control parameters
        self.activateCameraCheckbox = new CheckBox({
          name: "activateCamera",
          value: activateCamera,
          checked: activateCamera,
        });
        dojo.query("div.activateCamera", self.controlToolTip.domNode)[0].appendChild(self.activateCameraCheckbox.domNode);
        
        self.videoCompressionSelect = new Select({
          name: "videoCompression",
          value: videoCompression,
          options: videoCompressions,
        });
        dojo.query("div.videoCompression", self.controlToolTip.domNode)[0].appendChild(self.videoCompressionSelect.domNode);

        self.videoFramerateSpinner = new NumberSpinner({
          name: "videoFramerate",
          value: videoFramerate,
          style: "width: 50px"
        });
        dojo.query("div.videoFramerate", self.controlToolTip.domNode)[0].appendChild(self.videoFramerateSpinner.domNode);

        self.videoWidthSpinner = new NumberSpinner({
          name: "videoWidth",
          value: videoWidth,
          style: "width: 50px"
        });
        dojo.query("div.videoWidth", self.controlToolTip.domNode)[0].appendChild(self.videoWidthSpinner.domNode);

        self.videoHeightSpinner = new NumberSpinner({
          name: "videoHeight",
          value: videoHeight,
          style: "width: 50px"
        });
        dojo.query("div.videoHeight", self.controlToolTip.domNode)[0].appendChild(self.videoHeightSpinner.domNode);

        self.openMicrophoneCheckbox = new CheckBox({
          name: "openMicrophone",
          value: openMicrophone,
          checked: openMicrophone,
        });
        dojo.query("div.openMicrophone", self.controlToolTip.domNode)[0].appendChild(self.openMicrophoneCheckbox.domNode);
        
        self.audioEncodingSelect = new Select({
          name: "audioEncoding",
          value: audioEncoding,
          options: audioEncodings,
        });
        dojo.query("div.audioEncoding", self.controlToolTip.domNode)[0].appendChild(self.audioEncodingSelect.domNode);

        // session scoped parameters
        self.enableAudioCheckbox = new CheckBox({
          name: "enableAudio",
          value: enableAudio,
          checked: enableAudio,
        });
        dojo.query("div.enableAudio", self.controlToolTip.domNode)[0].appendChild(self.enableAudioCheckbox.domNode);

        self.showVideo = new CheckBox({
          name: "showVideo",
          value: showVideo,
          checked: showVideo,
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
