#ifndef OPENALINVOKER_H_W09J90F0
#define OPENALINVOKER_H_W09J90F0

#include "uscxml/config.h"
#include <uscxml/Interpreter.h>
#include "OpenALPlayer.h"

#include "PCMConverter.h"
#ifdef LIBSNDFILE_FOUND
#	include "LibSoundFile.h"
#else
#	ifdef AUDIOTOOLBOX_FOUND
#	include "AudioToolbox.h"
#	endif
#endif

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OpenALSource {
public:
	OpenALSource();
	~OpenALSource();

	OpenALPlayer* player;
	char buffer[ALPLAY_AUDIO_BUFFER_SIZE];
	bool loop;
	bool finished;
	int read;
	int written;
	float pos[3];
	URL file;
	PCMConverter* transform;
};

class OpenALInvoker : public InvokerImpl {
public:
	OpenALInvoker();
	virtual ~OpenALInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("openal");
		names.insert("spatial-audio");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#openal");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
	std::map<std::string, OpenALSource*> _sources;
	ALCcontext* _alContext;
	ALCdevice* _alDevice;

	tthread::recursive_mutex _mutex;
	tthread::thread* _thread;
	tthread::condition_variable _sourcesAvailable;

	bool _isStarted;
	bool _isRunning;
	float _listenerPos[3];

	static void fillBuffers(void* userdata);
	void start();

	void notifyOfEnd(OpenALSource*);
	void notifyOfLoop(OpenALSource*);

	float posToRadian(const std::string& pos);
	void getPosFromParams(const std::multimap<std::string, std::string>& params, float* position);

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OpenALInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: OPENALINVOKER_H_W09J90F0 */
