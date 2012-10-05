#ifndef SPATIALAUDIO_H_EH11SAQC
#define SPATIALAUDIO_H_EH11SAQC

#include <map>

#include "uscxml/Utilities.h"
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
  
  virtual Data getDataModelVariables();
  virtual void send(SendRequest& req);
  virtual void cancel(const std::string sendId);
  virtual void invoke(InvokeRequest& req);
  virtual void sendToParent(SendRequest& req);

  void setPosFromParams(std::map<std::string, std::string>& params);
  static float posToRadian(std::string& position);

protected:
  std::string _invokeId;
  Interpreter* _invokedInterpreter;
  
  URL_FILE* _urlHandle;
  
  float* _pos;
  bool _audioDevOpen;
  int _audioDevIndex;
  struct miles_audio_device* _audioDev;

};
	
}

#endif /* end of include guard: SPATIALAUDIO_H_EH11SAQC */
