// taken from http://trac.osgeo.org/openlayers/wiki/GreatCircleAlgorithms
var EARTH_RADIUS = 3958.75;
var PI = 3.1415926535897932384626433832795;
var DEG2RAD =  0.01745329252;
var RAD2DEG = 57.29577951308;

function WGS84Distance(x1, y1, x2, y2) {
	x1 = x1 * DEG2RAD;
  y1 = y1 * DEG2RAD;
  x2 = x2 * DEG2RAD;
  y2 = y2 * DEG2RAD;
  
	var a = sin(( y2-y1 ) / 2.0 )^2;
  var b = sin(( x2-x1 ) / 2.0 )^2;
  var c = sqrt( a + cos( y2 ) * cos( y1 ) * b );

  return 2 * asin( c ) * EARTH_RADIUS;
}

function WGS84Bearing(x1, y1, x2, y2) {
	x1 = x1 * DEG2RAD;
  y1 = y1 * DEG2RAD;
  x2 = x2 * DEG2RAD;
  y2 = y2 * DEG2RAD;

  var a = cos(y2) * sin(x2 - x1);
  var b = cos(y1) * sin(y2) - sin(y1) * cos(y2) * cos(x2 - x1);
  var adjust = 0;
  
	if((a == 0) && (b == 0)) {
      bearing = 0;
  } else if( b == 0) {
      if( a < 0)  
          bearing = 3 * PI / 2;
      else
          bearing = PI / 2;
  } else if( b < 0) 
      adjust = PI;
  else {
      if( a < 0) 
          adjust = 2 * PI;
      else
          adjust = 0;
  }
  return (atan(a/b) + adjust) * RAD2DEG;
}
