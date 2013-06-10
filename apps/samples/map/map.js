function Map(element) {

  // private attributes
  var self = this;
  
  // private instanceId
  if (!Map.instances)
    Map.instances = 0;
  var instanceId = Map.instances++;
  
  // public attributes
  this.coords = {};


  require([
    "dojo/ready",
    "dojo/dom-construct",
    "dojo/_base/window",
    "dojo/dom", 
    "dojox/geo/openlayers/Map",
    "dojox/geo/openlayers/GfxLayer",
    "dojox/geo/openlayers/Layer",
    "dojox/geo/openlayers/GeometryFeature",
    "dojox/geo/openlayers/Point",
    "dojox/geo/openlayers/LineString",
    "dojox/geo/openlayers/WidgetFeature",
    "dojox/charting/widget/Chart",
    "dojox/charting/widget/Chart2D", 
    "dojox/charting/plot2d/Pie",
    "dojox/charting/themes/PlotKit/blue"
    ], function(
      ready, 
      domConstruct,
      win,
      dom, 
      Map,
      GfxLayer,
      Layer,
      GeometryFeature,
      Point,
      LineString,
      WidgetFeature,
      Chart,
      Chart2D,
      Pie,
      blue
    ) {
    ready(function(){

      if (typeof(element) === 'string') {
        element = dom.byId(element);
      }
      
      element.style.width = "450px";
      element.style.height = "350px";
      
      var options = {
          baseLayerName: "WorldMap",
          baseLayerType : dojox.geo.openlayers.BaseLayerType.OSM,
          //baseLayerUrl: "http://localhost/mapserver/mapserv.cgi?map=./world.map",
          baseLayerOptions: {
              layers: ['contry','state','city','town','highway']
          },
          touchHandler: false,
          accessible: true
      };
      
      // Available base layers: http://dojotoolkit.org/reference-guide/1.7/dojox/geo/openlayers.html#id5
      self.map = new Map(element, options);
      
      // This is New York location
      var ny = {
        latitude : 49.877648,
        longitude : 8.654762
      };
      
      var people = [ {
         name : 'Dirk',
         y : 49.877848,
         x : 8.653762
      }, {
         name : 'Stefan',
         y : 49.877348,
         x : 8.655462
      } ];
      
      var div = domConstruct.create("div", {}, win.body());
      //var div = domConstruct.create("div", {});
      var chart = new Chart({
        margins : {
          l : 0,
          r : 0,
          t : 0,
          b : 0
        }
      }, div);
      
      var c = chart.chart;
      c.addPlot("default", {
        type : "Pie",
        radius : 50,
        labelOffset : 100,
        fontColor : "black",
        fontSize : 20
      });

      var ser = [ 2, 8, 12, 3 ];
      c.addSeries("Series", ser);
      c.setTheme(blue);
      c.render();
      c.theme.plotarea.fill = undefined;

      var descr = {
        longitude : ny.longitude,
        latitude : ny.latitude,
        widget : chart,
        width : 120,
        height : 120
      };
      feat3 = new WidgetFeature(descr);
      
      // create a GfxLayer
      var layer = new GfxLayer();
      
      var point = new Point({
          x:ny.longitude, 
          y:ny.latitude
      });
      // create a GeometryFeature
      var feat = new GeometryFeature(point);
      // set the shape properties, fill and stroke            
      feat.setFill([ 0, 128, 128 ]);
      feat.setStroke([ 0, 0, 0 ]);
      feat.setShapeProperties({
          r : 8
      });
      
      var pts = new LineString(people);
      // create a GeometryFeature
      var feat2 = new GeometryFeature(pts);
      // set the shape stroke property
      feat2.setStroke([ 0, 0, 0 ]);
      
      // add the feature to the layer
      layer.addFeature(feat);
      layer.addFeature(feat2);
      layer.addFeature(feat3);
      // add layer to the map
      self.map.addLayer(layer);
      
      // fit to New York with 0.1 degrees extent
      self.map.fitTo({
        position : [ ny.longitude, ny.latitude ],
        extent : 0.001
      });
    });
  });
}
