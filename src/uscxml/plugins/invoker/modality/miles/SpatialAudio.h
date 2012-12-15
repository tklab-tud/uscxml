#ifndef SPATIALAUDIO_H_EH11SAQC
#define SPATIALAUDIO_H_EH11SAQC

#include <map>

#include "../MMIComponent.h"

extern "C" {
# include "miles/audio.h"
# include "miles/audio_codec.h"
# include "miles/audio_device.h"
}

namespace uscxml {

class Interpreter;
  
class SpatialAudio : public MMIComponent {
public:
	SpatialAudio();
  virtual ~SpatialAudio();
  virtual Invoker* create(Interpreter* interpreter);
  
	virtual std::set<std::string> getNames() { 
		std::set<std::string> names;
		names.insert("spatial-audio");
		names.insert("audio");
		names.insert("http://www.smartvortex.eu/mmi/spatial-audio");
		names.insert("http://www.smartvortex.eu/mmi/spatial-audio/");
		return names;
	}

  virtual Data getDataModelVariables();
  virtual void send(SendRequest& req);
  virtual void cancel(const std::string sendId);
  virtual void invoke(InvokeRequest& req);
  virtual void sendToParent(SendRequest& req);

  void getPosFromParams(std::map<std::string, std::list<std::string> >& params, float* position);
  static float posToRadian(std::string& position);

protected:
  std::string _invokeId;
  Interpreter* _invokedInterpreter;
  
  std::stringstream _dataStream;
  
  float* _pos;
  float* _listener;
  bool _audioDevOpen;
  int _audioDevIndex;
  struct miles_audio_device* _audioDev;

};
	
}

#endif /* end of include guard: SPATIALAUDIO_H_EH11SAQC */
