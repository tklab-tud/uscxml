#ifndef SPATIALAUDIO_H_EH11SAQC
#define SPATIALAUDIO_H_EH11SAQC

#include <map>
#include <uscxml/Interpreter.h>

extern "C" {
#include "miles/audio_device.h"
#include "miles/audio_codec.h"
#include "miles/audio_io.h"
#include "miles/miles.h"
}

namespace uscxml {

class SpatialAudio : public InvokerImpl {
public:
	SpatialAudio();
	virtual ~SpatialAudio();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("spatial-audio");
		names.insert("audio");
		names.insert("http://www.smartvortex.eu/mmi/spatial-audio");
		names.insert("http://www.smartvortex.eu/mmi/spatial-audio/");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);
	virtual void sendToParent(SendRequest& req);

	void getPosFromParams(const std::multimap<std::string, std::string>& params, float* position);
	static float posToRadian(const std::string& position);

protected:
	std::string _invokeId;
	Interpreter* _invokedInterpreter;

	std::stringstream _dataStream;

	float* _pos;
	float* _listener;
	float* _maxPos;
	bool _audioDevOpen;
	int _audioDevIndex;
	struct miles_audio_device* _audioDev;

};

}

#endif /* end of include guard: SPATIALAUDIO_H_EH11SAQC */
