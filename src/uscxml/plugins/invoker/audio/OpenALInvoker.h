/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

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
	ALfloat pos[3];
	URL file;
	PCMConverter* transform;
};

class OpenALInvoker : public InvokerImpl {
public:
	OpenALInvoker();
	virtual ~OpenALInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("openal");
		names.push_back("spatial-audio");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#openal");
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
	ALfloat _listenerPos[3];
	ALfloat _listenerVel[3];
	ALfloat _listenerOrient[6];
	float _maxPos[3];

	static void fillBuffers(void* userdata);
	void start();

	void notifyOfEnd(OpenALSource*);
	void notifyOfLoop(OpenALSource*);

	float posToRadian(const std::string& pos);
	void getPosFromParams(const std::multimap<std::string, Data>& params, float* position);

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OpenALInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: OPENALINVOKER_H_W09J90F0 */
