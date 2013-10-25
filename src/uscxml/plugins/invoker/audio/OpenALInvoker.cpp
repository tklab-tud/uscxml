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

// see http://stackoverflow.com/questions/6563810/m-pi-works-with-math-h-but-not-with-cmath-in-visual-studio
#define _USE_MATH_DEFINES
#include <cmath>

#include <boost/algorithm/string.hpp>

#include "OpenALInvoker.h"
#include <uscxml/config.h>
#include <glog/logging.h>
#include <limits.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new OpenALInvokerProvider() );
	return true;
}
#endif

// see http://stackoverflow.com/questions/1904635/warning-c4003-and-errors-c2589-and-c2059-on-x-stdnumeric-limitsintmax
#undef max

OpenALInvoker::OpenALInvoker() {
	_isStarted = false;
	_alContext = NULL;
	_alDevice = NULL;
	_thread = NULL;
	_listenerPos[0] = _listenerPos[1] = _listenerPos[2] = 0;
	_listenerVel[0] = _listenerVel[1] = _listenerVel[2] = 0;
	_maxPos[0] = _maxPos[1] = _maxPos[2] = 1;

	_listenerOrient[0] = _listenerOrient[1] = _listenerOrient[3] = _listenerOrient[5] = 0;
	_listenerOrient[2] = _listenerOrient[4] = 1.0;
}

OpenALInvoker::~OpenALInvoker() {
	if (_thread) {
		_isStarted = false;
		_sourcesAvailable.notify_all();
		_thread->join();
		delete(_thread);
	}
	if (_alContext) {
//		alcCloseDevice(alcGetContextsDevice(_alContext));
//		alcDestroyContext(_alContext);
	}
};

boost::shared_ptr<InvokerImpl> OpenALInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<OpenALInvoker> invoker = boost::shared_ptr<OpenALInvoker>(new OpenALInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data OpenALInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void OpenALInvoker::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	if (!_isStarted)
		start();

	if (boost::iequals(req.name, "play")) {
		if (req.params.find("src") == req.params.end()) {
			LOG(ERROR) << "Sent event play with no src URL";
		}

		URL srcURL = req.params.find("src")->second.atom;
		if (!srcURL.toAbsolute(_interpreter->getBaseURI())) {
			LOG(ERROR) << "src URL " << req.params.find("src")->second << " is relative with no base URI set for interpreter";
			return;
		}

		_sources[req.sendid] = new OpenALSource();
		_sources[req.sendid]->loop = req.params.find("loop") != req.params.end() && boost::iequals(req.params.find("loop")->second.atom, "true");
		_sources[req.sendid]->file = srcURL;
#ifdef LIBSNDFILE_FOUND
		_sources[req.sendid]->transform	= new LibSoundFile(srcURL.asLocalFile(".audio"));
#else
#	ifdef AUDIOTOOLBOX_FOUND
		_sources[req.sendid]->transform	= new AudioToolbox(srcURL.asLocalFile(".audio"));
#	endif
#endif
		if (_sources[req.sendid]->transform == NULL) {
			LOG(ERROR) << "No transcoder for input file known - install libsndfile or AudioToolbox";
			_sources.erase(req.sendid);
			return;
		}

		// force mono format to ensure actual spatial audio
		PCMFormat format = _sources[req.sendid]->transform->getInFormat();
		format.alFormat = AL_FORMAT_MONO16;
		_sources[req.sendid]->transform->setOutFormat(format);

		try {
			_sources[req.sendid]->player = new OpenALPlayer(_alContext, NULL, format.alFormat, format.sampleRate);
		} catch (std::exception ex) {
			returnErrorExecution(ex.what());
			return;
		}

		getPosFromParams(req.params, _sources[req.sendid]->pos);

		_sources[req.sendid]->pos[0] -= _listenerPos[0];
		_sources[req.sendid]->pos[1] -= _listenerPos[1];
		_sources[req.sendid]->pos[2] -= _listenerPos[2];
		try {
			_sources[req.sendid]->player->setPosition(_sources[req.sendid]->pos);

		} catch (std::exception ex) {
			returnErrorExecution(ex.what());
		}

		_sourcesAvailable.notify_all();
	}

	if (boost::iequals(req.name, "move.source")) {
		std::string sourceId;
		if (req.params.find("source") == req.params.end()) {
			LOG(WARNING) << "Cannot move source with no source given in parameters";
			return;
		}
		sourceId = req.params.find("source")->second.atom;

		if (_sources.find(sourceId) == _sources.end()) {
			LOG(WARNING) << "Given source '" << sourceId << "' not active or not existing";
			return;
		}

		getPosFromParams(req.params, _sources[sourceId]->pos);
		try {
			_sources[sourceId]->player->setPosition(_sources[sourceId]->pos);
		} catch (std::exception ex) {
			returnErrorExecution(ex.what());
		}
	}

	if (boost::iequals(req.name, "move.listener")) {
		getPosFromParams(req.params, _listenerPos);

		try {
			alcMakeContextCurrent(_alContext);
			alListenerfv(AL_POSITION, _listenerPos);
			OpenALPlayer::checkOpenALError(__LINE__);
		} catch (std::exception ex) {
			returnErrorExecution(ex.what());
		}
	}

}

void OpenALInvoker::start() {
	_isStarted = true;
	_thread = new tthread::thread(&OpenALInvoker::fillBuffers, this);
}

void OpenALInvoker::fillBuffers(void* userdata) {
	OpenALInvoker* INST = (OpenALInvoker*)userdata;
	while(INST->_isStarted) {
		// do nothing until we have at least one source
		int waitMs = std::numeric_limits<int>::max();
		INST->_mutex.lock();
		while (INST->_sources.size() == 0 && INST->_isStarted) {
			INST->_sourcesAvailable.wait(INST->_mutex);
		}

		if (!INST->_isStarted)
			return;

		// here we are with at least one source and a locked mutex
		assert(INST->_sources.size() > 0);

		std::map<std::string, OpenALSource*>::iterator srcIter = INST->_sources.begin();
		while(srcIter != INST->_sources.end()) {
			OpenALSource* src = srcIter->second;
			int wait = std::numeric_limits<int>::max();

			if (src->finished) {
				// source has already finished playing, feed no more samples to it
				try {
					wait = src->player->isPlaying();
					if (wait == 0) {
						// source stopped playing, delete it
						INST->notifyOfEnd(src);
						delete src;
						INST->_sources.erase(srcIter++);
						continue;
					} else {
						// source returned time when to repoll
						assert(wait > 0);
					}
				} catch (std::exception ex) {
					INST->returnErrorExecution(ex.what());
					delete src;
					INST->_sources.erase(srcIter++);
					continue;
				}
			} else {
				// source still needs more samples or play existing buffer
				if (src->written == src->read) {
					// all read samples have been written, read some more
					src->written = 0;
					src->read = src->transform->read(src->buffer, ALPLAY_AUDIO_BUFFER_SIZE);
					if (src->read < ALPLAY_AUDIO_BUFFER_SIZE) {
						if (src->loop) {
							INST->notifyOfLoop(src);
							while (src->read < ALPLAY_AUDIO_BUFFER_SIZE) {
								src->transform->seek(0);
								src->read += src->transform->read(src->buffer + src->read, ALPLAY_AUDIO_BUFFER_SIZE - src->read);
							}
						} else {
							src->finished = true;
							memset(src->buffer + src->read, 0, ALPLAY_AUDIO_BUFFER_SIZE - src->read);
						}
					}
				}

				// there are unwritten samples in the buffer
				if (src->read != src->written) {
					try {
						int written = src->player->write(src->buffer, ALPLAY_AUDIO_BUFFER_SIZE, &wait);
						if (written >=0 ) {
							src->written += written;
						}
					} catch (std::exception ex) {
						INST->returnErrorExecution(ex.what());
						src->finished = true;
					}
				} else {
					assert(src->finished);
				}
			}

			waitMs = (wait < waitMs ? wait : waitMs);
			srcIter++;
		}

//		std::cout << "W" << waitMs << ".";

		INST->_mutex.unlock();
		if (waitMs < std::numeric_limits<int>::max())
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(waitMs));
	}
}

void OpenALInvoker::cancel(const std::string sendId) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

}

void OpenALInvoker::invoke(const InvokeRequest& req) {
	_alDevice = alcOpenDevice(NULL);
	if (_alDevice == NULL) {
		throw std::string("__FILE__ __LINE__ openal error opening device");
	}

	std::multimap<std::string, Data>::const_iterator paramIter = req.params.begin();
	while(paramIter != req.params.end()) {
		if (boost::iequals(paramIter->first, "maxX"))
			_maxPos[0] = strTo<float>(paramIter->second.atom);
		if (boost::iequals(paramIter->first, "maxY"))
			_maxPos[1] = strTo<float>(paramIter->second.atom);
		if (boost::iequals(paramIter->first, "maxZ"))
			_maxPos[2] = strTo<float>(paramIter->second.atom);
		paramIter++;
	}

	// create new context with device
	_alContext = alcCreateContext (_alDevice, NULL);
	if (_alContext == NULL) {
		alcCloseDevice (_alDevice);
		throw std::string("openal error create context");
	}

//	std::cout << boost::lexical_cast<std::string>(_alContext);
//	std::cout << boost::lexical_cast<std::string>(_alDevice);

	alcMakeContextCurrent(_alContext);
//	float listener[3] = {0,0,0};
//	alListenerfv(AL_POSITION, listener);

	alcMakeContextCurrent(_alContext);
	alListenerfv(AL_POSITION, _listenerPos);
	alListenerfv(AL_VELOCITY, _listenerVel);
	alListenerfv(AL_ORIENTATION, _listenerOrient);

	alListenerf(AL_GAIN, 0.5);

	start();
}

void OpenALInvoker::notifyOfEnd(OpenALSource* src) {
	Event ev;
	ev.name = "audio.end";
	ev.data.compound["file"] = src->file;
	returnEvent(ev);
}

void OpenALInvoker::notifyOfLoop(OpenALSource* src) {
	Event ev;
	ev.name = "audio.loop";
	ev.data.compound["file"] = src->file;
	returnEvent(ev);
}

void OpenALInvoker::getPosFromParams(const std::multimap<std::string, Data>& params, float* position) {
	// vector explicitly given
	try {
		if (params.find("x") != params.end())
			position[0] = boost::lexical_cast<float>(params.find("x")->second);
		if (params.find("y") != params.end())
			position[1] = boost::lexical_cast<float>(params.find("y")->second);
		if (params.find("z") != params.end())
			position[2] = boost::lexical_cast<float>(params.find("z")->second);
	} catch (boost::bad_lexical_cast& e) {
		LOG(ERROR) << "Cannot interpret x, y or z as float value in params: " << e.what();
	}

	try {
		// right is an alias for x
		if (params.find("right") != params.end())
			position[0] = boost::lexical_cast<float>(params.find("right")->second);
		// height is an alias for y
		if (params.find("height") != params.end())
			position[1] = boost::lexical_cast<float>(params.find("height")->second);
		// front is an alias for z
		if (params.find("front") != params.end())
			position[2] = boost::lexical_cast<float>(params.find("front")->second);
	} catch (boost::bad_lexical_cast& e) {
		LOG(ERROR) << "Cannot interpret right, height or front as float value in params: " << e.what();
	}

	// do we have a position on a circle?
	try {
		if (params.find("circle") != params.end()) {
			float rad = posToRadian(params.find("circle")->second);
			position[0] = cosf(rad);
			position[2] = -1 * sinf(rad); // z axis increases to front
//			position[0] *= 150;
//			position[2] *= 150;

		}
	} catch (boost::bad_lexical_cast& e) {
		LOG(ERROR) << "Cannot interpret circle as float value in params: " << e.what();
	}

	position[0] = position[0] / _maxPos[0];
	position[1] = position[1] / _maxPos[1];
	position[2] = position[2] / _maxPos[2];
//	std::cout << position[0] << ":" << position[1] << ":" << position[2] << std::endl;

}

float OpenALInvoker::posToRadian(const std::string& pos) {

	std::string trimmedPos = boost::trim_copy(pos);
	float rad = 0;

	if (trimmedPos.size() > 3 && boost::iequals("deg", trimmedPos.substr(trimmedPos.length() - 3, 3))) {
		rad = boost::lexical_cast<float>(trimmedPos.substr(0, trimmedPos.size() - 3));
		rad = fmodf(rad, 360); // into range [0-360]
		rad /= 180; // into range [0-2]
		rad *= M_PI; // into range [0-2PI]
		rad -= M_PI_2; // 0 to top;
		rad *= -1; // make clockwise
		rad += 2 * M_PI; // make positive
	} else if (trimmedPos.size() > 3 && boost::iequals("rad", trimmedPos.substr(trimmedPos.length() - 3, 3))) {
		rad = boost::lexical_cast<float>(trimmedPos.substr(0, trimmedPos.size() - 3));
		rad = fmodf(rad, M_PI * 2); // into range [0-2*PI]
	} else {
		LOG(ERROR) << "Cannot make sense of position value " << trimmedPos << ": does not end in 'deg', 'rad'";
	}
	return rad;
}

OpenALSource::OpenALSource() {
	pos[0] = pos[1] = pos[2] = 0;
	player = NULL;
	loop = false;
	finished = false;
	transform = NULL;
	read = written = 0;
	memset(buffer, 0, ALPLAY_AUDIO_BUFFER_SIZE);
}

OpenALSource::~OpenALSource() {
	if (player)
		delete player;
	if (transform)
		delete transform;
}

}