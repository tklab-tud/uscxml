function Annotations(element, params) {
		
	// private attributes
	var self = this;
	var dojo               = require("dojo");
	var domConst           = dojo.require('dojo/dom-construct');
	var xhr                = dojo.require("dojo/_base/xhr");

  if (typeof(element) === 'string') {
    element = dojo.byId(element);
  }

  // private instanceId
  if (!Annotations.instances)
  	Annotations.instances = 0;
  var instanceId = Annotations.instances++;
  
  // public attributes
  this.annotations = [];
  this.vrmlViewer = params.viewer;

  // establish our dom
	element.appendChild(domConst.toDom('\
    <div style="text-align: right"><div class="annotation" /></div><button type="button" class="annotate"></button></div>\
	  <div class="messages"></div>\
	'));
  
  this.annotationTextElem = dojo.query("div.annotation", element)[0];
	this.annotateButtonElem = dojo.query("button.annotate", element)[0];
	this.messagesElem = dojo.query("div.messages", element)[0];
	
	// privileged public methods
	this.annotate = function(text) {
    var pose = self.vrmlViewer.pose;
    var imageURL = self.imageURL;
    var annoLink = document.createElement("a");
    annoLink.setAttribute("href", "#");
    var annoText = document.createTextNode(text + "\n");
    annoLink.appendChild(annoText);
    annoLink.onclick = function() {
      self.vrmlViewer.pose = pose;
      self.vrmlViewer.imageURL = imageURL;
      self.vrmlViewer.updateScene();
    }
	  this.messagesElem.appendChild(annoLink);
	}

	require(["dijit/form/TextBox"], function(TextBox) {
  	self.annotationBox = new TextBox({
      name: "Annotation",
  		style: "width: 70%",
  		onKeyDown: function(e) {
        var code = e.keyCode || e.which;
        if( code === 13 ) {
          e.preventDefault();
    		  self.annotate(this.get("value"));
          return false; 
        }
  		},
  	}, self.annotationTextElem);
  });
  
  require(["dijit/form/Button"], function(Button) {
  	self.resetButton = new Button({
      label: "Annotate",
  		onClick: function(){
  		  self.annotate(self.annotationBox.get("value"));
  		}
  	}, self.annotateButtonElem);
  });
  
}
