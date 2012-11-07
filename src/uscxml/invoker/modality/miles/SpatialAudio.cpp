#include "uscxml/Common.h"
#include "SpatialAudio.h"
#include "uscxml/Interpreter.h"
#include "uscxml/URL.h"

#include <glog/logging.h>

#ifdef _WIN32
#define _USE_MATH_DEFINES
#endif
#include <math.h>

namespace uscxml {
	
SpatialAudio::SpatialAudio() {
  _audioDevOpen = false;
  _audioDev = NULL;
  _audioDevIndex = -1;
  _pos = new float[3];
  _pos[0] = _pos[1] = _pos[2] = 0.0;
  _listener = new float[3];
  _listener[0] = _listener[1] = _listener[2] = 0.0;
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
//  data.compound["foo"] = Data("32");
  return data;
}

void SpatialAudio::send(SendRequest& req) {
  if (!_audioDevOpen) {
    _audioDev = miles_audio_device_open(_audioDevIndex, 0, 22050, 2, 1, 0);
    if (_audioDev != NULL) {
      _audioDevOpen = true;
      float rolloffFactor = 0.2;
      miles_audio_device_control(_audioDev, MILES_AUDIO_DEVICE_CTRL_SET_ROLLOFF_FACTOR, &rolloffFactor);
    }
  }
    
  if (boost::iequals(req.name, "play")) {
    if (_audioDevOpen) {
      getPosFromParams(req.params, _pos);

//      std::cout << "Source: ";
//      for (int i = 0; i < 3; i++) {
//        std::cout << _pos[i] << " ";
//      }
//      std::cout << std::endl;
      
      miles_audio_device_control(_audioDev, MILES_AUDIO_DEVICE_CTRL_SET_POSITION, _pos);
      
      char* buffer = (char*)malloc(_audioDev->chunk_size);
      // skip wav header
      _dataStream.seekg(44);

      while(_dataStream.readsome(buffer, _audioDev->chunk_size) != 0) {
        miles_audio_device_write(_audioDev, buffer, _audioDev->chunk_size);
      }
      free(buffer);
    }
  } else if (boost::iequals(req.name, "move.listener")) {
    if (_audioDevOpen) {
      getPosFromParams(req.params, _listener);

      std::cout << "Listener: ";
      for (int i = 0; i < 3; i++) {
        std::cout << _listener[i] << " ";
      }
      std::cout << std::endl;
      
      miles_audio_device_control(_audioDev, MILES_AUDIO_DEVICE_CTRL_SET_LISTENER_POS, _listener);

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
    Arabica::io::URI url(req.src);
    if (!_interpreter->makeAbsolute(url)) {
      LOG(ERROR) << "Source attribute for audio invoker has relative URI " << req.src << " with no base URI set for interpreter";
      return;
    }
    
   	URL scriptUrl(url.as_string());
    _dataStream << scriptUrl;
  }

  getPosFromParams(req.params, _pos);

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

  void SpatialAudio::getPosFromParams(std::map<std::string, std::list<std::string> >& params, float* position) {
  // vector explicitly given
  try {
    if (params.find("x") != params.end())
      position[0] = boost::lexical_cast<float>(params["x"].front());
    if (params.find("y") != params.end())
      position[1] = boost::lexical_cast<float>(params["y"].front());
    if (params.find("z") != params.end())
      position[2] = boost::lexical_cast<float>(params["z"].front());
  } catch (boost::bad_lexical_cast& e) {
    LOG(ERROR) << "Cannot interpret x, y or z as float value in params: " << e.what();
  }
  
  try {
    // right is an alias for x
    if (params.find("right") != params.end())
      position[0] = boost::lexical_cast<float>(params["right"].front());
    // height is an alias for y
    if (params.find("height") != params.end())
      position[1] = boost::lexical_cast<float>(params["height"].front());
    // front is an alias for z
    if (params.find("front") != params.end())
      position[2] = boost::lexical_cast<float>(params["front"].front());
  } catch (boost::bad_lexical_cast& e) {
    LOG(ERROR) << "Cannot interpret right, height or front as float value in params: " << e.what();
  }

  // do we have a position on a circle?
  try {
    if (params.find("circle") != params.end()) {
      float rad = posToRadian(params["circle"].front());
      position[0] = cosf(rad);
      position[2] = -1 * sinf(rad); // z axis increases to front
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