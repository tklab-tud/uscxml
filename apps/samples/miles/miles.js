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

  // private attributes
  var scxmlURL    = "127.0.0.1:8080"
  var reflectorIp = "127.0.0.1"
  var email       = "me@somehost.de";
  var problemName = "some really hard problem";
  
  // override with parameters if given
  this.params = params;
  if (params && params.scxmlURL)     scxmlURL = params.scxmlURL;
  if (params && params.reflectorIp)  reflectorIp = params.reflectorIp;
  if (params && params.email)        email = params.email;
  if (params && params.problemName)  problemName = params.problemName;

  this.connect = function() {
    self.xhr.post({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/connect",
      handleAs:"json",
      postData: dojo.toJson({
        reflectorIp: reflectorIp,
        email: email,
        problemName: problemName
      }),
      headers:{
        "X-Requested-With": null,
        "Content-Type": "application/json",
      },
      load: function(result) {
        // we expect nothing in return
        self.connected = true;
        // trigger continuously loading the image
        refreshImage();
      }
    });  
  }

  var refreshImage = function() {
    self.xhr.get({
      // The URL to request
      url: "http://" + scxmlURL + "/miles/image",
      handleAs:"text",
      postData: dojo.toJson({
        reflectorIp: reflectorIp,
        email: email,
        problemName: problemName
      }),
      headers:{
        "X-Requested-With": null,
        "Content-Type": "application/json",
      },
      load: function(result) {
        self.pictureElem.src = "data:image/jpeg;base64," + result;
        if (self.connected) {
          self.messageElem.innerHTML = self.imageIteration++;
          refreshImage();
        }
      }
    });  
    
  };

  require(["dojo/dom-construct", 
           "dojo/_base/xhr", 
           "dojo/dom",
           "dijit/form/DropDownButton",
           "dijit/TooltipDialog",
           "dojo/ready"], 
    function(domConst, 
             xhr, 
             dom,
             DropDownButton,
             TooltipDialog,
             ready) {      
      ready(function() {
        self.xhr = xhr;
        
        if (typeof(element) === 'string') {
          element = dom.byId(element);
        }

        element.appendChild(domConst.toDom('\
          <table>\
            <tr>\
              <td valign="top">\
                  <div style="position: relative; padding: 0px">\
                    <img class="picture" src="test.jpeg"></img>\
                    <div style="position: absolute; left: 10px; top: 10px">\
                      <table></tr>\
                        <td class="control" style="vertical-align: middle"></td>\
                      </tr></table>\
                    </div>\
                  </div>\
              </td>\
            </tr>\
            <tr>\
              <td valign="top">\
                  <div class="messages" style="position: relative; padding: 0px">\
              </td>\
            </tr>\
          </table>\
        '));
        
        self.pictureElem = dojo.query("img.picture", element)[0];
        self.controlElem = dojo.query("td.control", element)[0];
        self.messageElem = dojo.query("div.messages", element)[0];
        
        // the control dropdown button
        self.controlDropDownContent = domConst.toDom('<div />');
        self.controlToolTip = new TooltipDialog({ content:self.controlDropDownContent, style:"max-height:320px"});
        self.controlDropDown = new DropDownButton({ label: "Connect", dropDown: self.controlToolTip });
        self.controlElem.appendChild(self.controlDropDown.domNode);
        
        self.connect();
        
      })
  });
}
