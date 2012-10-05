#include "SpatialAudio.h"
#include "uscxml/Interpreter.h"

#include <glog/logging.h>

#include <math.h>

namespace uscxml {
	
SpatialAudio::SpatialAudio() {
  _audioDevOpen = false;
  _audioDev = NULL;
  _audioDevIndex = -1;
  _pos = new float[3];
  _pos[0] = _pos[1] = _pos[2] = 0.0;
}

  
SpatialAudio::~SpatialAudio() {
};
  
Invoker* SpatialAudio::create(Interpreter* interpreter) {
  SpatialAudio* invoker = new SpatialAudio();
  invoker->_interpreter = interpreter;
  return invoker;
}

Data SpatialAudio::getDataModelVariables() {
  Data data;
  return data;
}

void SpatialAudio::send(SendRequest& req) {
  setPosFromParams(req.params);
  if (boost::iequals(req.name, "play")) {
    if (!_audioDevOpen) {
      _audioDev = miles_audio_device_open(_audioDevIndex, 0, 22050, 2, 1, 0);
    }
    if (_audioDev != NULL) {
      _audioDevOpen = true;
      miles_audio_device_control(_audioDev, MILES_AUDIO_DEVICE_CTRL_SET_POSITION, _pos);
      
      char* buffer = (char*)malloc(_audioDev->chunk_size);
      // skip wav header
      url_fread(buffer, 44, 1, _urlHandle);
      int read = 0;
      while((read = url_fread(buffer, _audioDev->chunk_size, 1, _urlHandle) != 0)) {
        miles_audio_device_write(_audioDev, buffer, _audioDev->chunk_size);
      }
      url_rewind(_urlHandle);
      free(buffer);
    }
  }
}

void SpatialAudio::cancel(const std::string sendId) {
  assert(false);
}

void SpatialAudio::sendToParent(SendRequest& req) {
  req.invokeid = _invokeId;
  assert(false);
}

void SpatialAudio::invoke(InvokeRequest& req) {
  _invokeId = req.invokeid;
  
  if (req.src.length() > 0) {
    _urlHandle = url_fopen(req.src.c_str(), "r");
    if(!_urlHandle) {
      LOG(ERROR) << "couldn't url_fopen() " << req.src;
    }
  }

  setPosFromParams(req.params);

  struct miles_audio_device_description *devices;
  int ndevs;
  
	ndevs = miles_audio_device_get_supported_devices(&devices);
  
  for (int i = 0; i < ndevs; i++) {
		if ((devices[i].capabilities & MILES_AUDIO_DEVICE_CAPABILITY_SPATIAL) &&
        (devices[i].capabilities & MILES_AUDIO_DEVICE_CAPABILITY_OUTPUT)) {
      _audioDevIndex = i;
      break;
    }
  }
}

void SpatialAudio::setPosFromParams(std::map<std::string, std::string>& params) {
  // vector explicitly given
  try {
    if (params.find("x") != params.end())
      _pos[0] = boost::lexical_cast<float>(params["x"]);
    if (params.find("y") != params.end())
      _pos[1] = boost::lexical_cast<float>(params["y"]);
    if (params.find("z") != params.end())
      _pos[2] = boost::lexical_cast<float>(params["z"]);
  } catch (boost::bad_lexical_cast& e) {
    LOG(ERROR) << "Cannot interpret x, y or z as float value in params: " << e.what();
  }
  
  try {
    // right is an alias for x
    if (params.find("right") != params.end())
      _pos[0] = boost::lexical_cast<float>(params["right"]);
    // height is an alias for y
    if (params.find("height") != params.end())
      _pos[1] = boost::lexical_cast<float>(params["height"]);
    // front is an alias for z
    if (params.find("front") != params.end())
      _pos[2] = boost::lexical_cast<float>(params["front"]);
  } catch (boost::bad_lexical_cast& e) {
    LOG(ERROR) << "Cannot interpret right, height or front as float value in params: " << e.what();
  }

  // do we have a position on a circle?
  try {
    if (params.find("circle") != params.end()) {
      float rad = posToRadian(params["circle"]);
      _pos[0] = cosf(rad);
      _pos[2] = -1 * sinf(rad); // z axis increases to front
    }
  } catch (boost::bad_lexical_cast& e) {
    LOG(ERROR) << "Cannot interpret circle as float value in params: " << e.what();
  }
//  std::cout << _pos[0] << ":" << _pos[1] << ":" << _pos[2] << std::endl;

}
  
float SpatialAudio::posToRadian(std::string& position) {
  boost::trim(position);
  float rad = 0;
  
  if (position.size() > 3 && boost::iequals("deg", position.substr(position.length() - 3, 3))) {
    rad = boost::lexical_cast<float>(position.substr(0, position.size() - 3));
    rad = fmodf(rad, 360); // into range [0-360]
    rad /= 180; // into range [0-2]
    rad *= M_PI; // into range [0-2PI]
    rad -= M_PI_2; // 0 to top;
    rad *= -1; // make clockwise
    rad += 2 * M_PI; // make positive
  } else if (position.size() > 3 && boost::iequals("rad", position.substr(position.length() - 3, 3))) {
    rad = boost::lexical_cast<float>(position.substr(0, position.size() - 3));
    rad = fmodf(rad, M_PI * 2); // into range [0-2*PI]
  } else {
    LOG(ERROR) << "Cannot make sense of position value " << position << ": does not end in 'deg', 'rad'";
  }
  return rad;
}
  
}