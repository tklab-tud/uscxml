#include "OpenALPlayer.h"
#include <assert.h>
#include <stdexcept>

tthread::recursive_mutex OpenALPlayer::_alMutex;

/**
* Create a new OpenAL stream source
*/
OpenALPlayer::OpenALPlayer(ALCcontext* context, OpenALPlayerCallback* audioCallback, ALenum format, ALsizei freq) {

	_isInitialized = false;
	_audioCallback = audioCallback;
	_freq = freq;
	_format = format;
	_bufferSize = 0;
	_nrBuffers = 0;
	_thread = NULL;
	_alId = 0;

	_position[0] = _position[1] = _position[2] = 0;
	_velocity[0] = _velocity[1] = _velocity[2] = 0;
	_direction[0] = _direction[1] = _direction[2] = 0;

	tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);
	if (context == NULL) {
		// this is in essence alutInit() from freealut.

		// use the current context if there is one
		_context = alcGetCurrentContext();

		if (_context == NULL) {
//			std::cout << "\tnew context" << std::endl;
			// create a new context if none was given and no is current

			// get default device
			ALCdevice* device = alcOpenDevice(NULL);
			if (device == NULL) {
				throw std::runtime_error("__FILE__ __LINE__ openal error opening device");
			}

			// create new context with device
			_context = alcCreateContext (device, NULL);
			if (_context == NULL) {
				alcCloseDevice (device);
				throw std::runtime_error("openal error create context");
			}

			// make context current
			if (!alcMakeContextCurrent (_context)) {
				alcDestroyContext (_context);
				alcCloseDevice (device);
				throw std::runtime_error("openal error make context current");
			}
		} else {
//			std::cout << "\texisting context" << std::endl;
		}
	} else {
//		std::cout << "\tgiven context" << std::endl;
		_context = context;
	}
}

OpenALPlayer::~OpenALPlayer() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);
	if (isPlaying()) {
		alSourceStop(_alId);
	}
	if (_thread) {
		stop();
		_thread->join();
		delete(_thread);
	}

	if (_isInitialized) {
		alDeleteSources(1, &_alId);
		if (alIsSource(_alId)) {
			throw std::runtime_error("openal source id still valid");
		}
		for (int i = 0; i < _nrBuffers; i++) {
			assert(alIsBuffer(_bufferIds[i]));
			free(_buffers[i]);
		}
		alDeleteBuffers(_nrBuffers, _bufferIds);
		for (int i = 0; i < _nrBuffers; i++) {
			assert(!alIsBuffer(_bufferIds[i]));
		}
		free(_buffers);
		free(_bufferIds);
	}
	// clear errors and begone
	alGetError();

}

/**
* Allocate; data and set defaults
*/
void OpenALPlayer::init() {
	_userData = NULL;
	_pitch = 0;
	_gain = 0;
	_referenceDistance = 1.0;
	_isLooping = false;

	// no one set a buffer size yet
	if (_bufferSize <= 0)
		_bufferSize = ALPLAY_AUDIO_BUFFER_SIZE;

	// no one set the number of buffers yet
	if (_nrBuffers <= 0)
		_nrBuffers = ALPLAY_NR_AUDIO_BUFFERS;

	_isInitialized = true;

	_buffers = (char**)malloc(_nrBuffers * sizeof(char*));
	_bufferIds = (ALuint*)malloc(_nrBuffers * sizeof(ALuint));
	for (int i = 0; i < _nrBuffers; i++) {
		_buffers[i] = 0; //(char*)malloc(_bufferSize);
	}

	// there are other formats as well and this will have to be extended
	int bytesPerSample = 2;
	switch(_format) {
	case AL_FORMAT_MONO8:
	case AL_FORMAT_STEREO8:
		bytesPerSample = 1;
		break;

	case AL_FORMAT_MONO16:
	case AL_FORMAT_STEREO16:
		bytesPerSample = 2;
		break;
	}

	// how many ms audio is in one buffer?
	_msForBuffer    = (int)(((float)_bufferSize / (float)bytesPerSample) / ((float)_freq / 1000.0f));
	_initialSleep   = (_msForBuffer - (int)(0.6 * _msForBuffer)) * _nrBuffers;
	_bufferSleep    =  _msForBuffer - (int)(0.4 * _msForBuffer);
	_repollSleep    =  _msForBuffer - (int)(0.7 * _msForBuffer);

//  std::cout << _msForBuffer << "ms in one buffer" << std::endl;

	// get available buffer ids
	tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);

	if (!alcMakeContextCurrent (_context)) {
		throw std::runtime_error("openal error make context current");
	}

	alGenBuffers(_nrBuffers, _bufferIds);
	checkOpenALError(__LINE__);

	// get new source id from openAL
	alGenSources(1, &_alId);

	checkOpenALError(__LINE__);
	if (!alIsSource(_alId)) {
		throw std::runtime_error("openal source id not valid");
	}

	// set our position and various flags to meaningful defaults
	alSourcei(_alId, AL_LOOPING, AL_FALSE);
	checkOpenALError(__LINE__);
	alSourcefv(_alId, AL_POSITION, _position);
	checkOpenALError(__LINE__);
	alSourcef(_alId,AL_REFERENCE_DISTANCE, 5.0f);
	checkOpenALError(__LINE__);
//	alDistanceModel(AL_LINEAR_DISTANCE);
//	checkOpenALError(__LINE__);
//	alSourcefv(_alId, AL_VELOCITY, _velocity);
//	checkOpenALError(__LINE__);
//	alSourcefv(_alId, AL_DIRECTION, _direction);
//	checkOpenALError(__LINE__);
//	alSourcef (_alId, AL_ROLLOFF_FACTOR,  1.0);
//	checkOpenALError(__LINE__);
	alSourcef(_alId,AL_REFERENCE_DISTANCE, 5.0f);
	checkOpenALError(__LINE__);
//	float listener[] = { 0.0, 0.0, 0.0 };
//	alListenerfv(AL_POSITION, listener);
//	checkOpenALError(__LINE__);

	alSourcei (_alId, AL_SOURCE_RELATIVE, AL_TRUE);
	checkOpenALError(__LINE__);
}

/**
* Start the sound source.
*
* This will trigger continuous calls top the audio callback.
*/
void OpenALPlayer::start() {
	if (!_isInitialized)
		init();

	if (_audioCallback == NULL)
		throw std::runtime_error("cannot start without an audio callback");

	_isStarted = true;

	// prime the buffers with some initial data and register for buffer ids
	tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);
	for (ALuint i = 0; i < (unsigned int)_nrBuffers; i++) {
		_buffers[i] = (char*)malloc(_bufferSize);
		_audioCallback->getSamples(_buffers[i], _bufferSize, this);
		alBufferData(_bufferIds[i], _format, _buffers[i], _bufferSize, _freq);
		checkOpenALError(__LINE__);
	}
	// enqueue all buffers
	alSourceQueueBuffers(_alId, _nrBuffers, _bufferIds);
	checkOpenALError(__LINE__);

	// start thread
	if (_audioCallback != NULL) {
		_thread = new tthread::thread(&OpenALPlayer::updateBuffersWrapper, this);
	}

	// tell openAL to start rendering the buffers
	alSourcePlay(_alId);
	checkOpenALError(__LINE__);
}

// find bufferId in _bufferIds to get bufferIndex into _buffers - messy
int OpenALPlayer::bufferIndex(int bufferId) {
	int bufferIndex = 0;
	for (; bufferIndex < _nrBuffers; bufferIndex++) {
		if (_bufferIds[bufferIndex] == (unsigned int)bufferId)
			break;
	}
	if (bufferIndex >= _nrBuffers)
		throw std::runtime_error("could not find dequeued bufferId in ids");
	return bufferIndex;
}

/**
* Write a buffer (blocking).
*
* This allows for a pushing model, whereas the callback allows for a polling model.
*/
int OpenALPlayer::write(char* buffer, int size, int* repollAt, bool blocking) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);

	if (!_isInitialized)
		init();

	if (_audioCallback != NULL) {
		throw std::runtime_error("you cannot use the write interface with an audio callback");
	}

	if (size != _bufferSize) {
		throw std::runtime_error("buffersize does not match");
	}

	if (!alcMakeContextCurrent (_context)) {
		throw std::runtime_error("openal error make context current");
	}

	// try to enqueue the given buffer data
	for (;;) {
		// do we have an empty buffer in the OpenAL queue?
		int processed;
		alGetSourcei(_alId, AL_BUFFERS_PROCESSED, &processed);
		checkOpenALError(__LINE__);

//		if (!isPlaying())
//			std::cout << "-";

		if (processed > 0) {
//			std::cout << "P" << processed;
			ALuint bufferId = 0;
			alSourceUnqueueBuffers(_alId, 1, &bufferId);
			checkOpenALError(__LINE__);

			int bufferIdx = bufferIndex(bufferId);

			// fill the buffer with the given data
			memcpy(_buffers[bufferIdx], buffer, _bufferSize);
			alBufferData(bufferId, _format, _buffers[bufferIdx], _bufferSize, _freq);
			checkOpenALError(__LINE__);

			// enqueue
			alSourceQueueBuffers(_alId, 1, &bufferId);
			checkOpenALError(__LINE__);

			// some buffers were processed
			if (repollAt)
				*repollAt = _repollSleep;
			break;

		} else {
			// no buffer processed - is there an uninitialized buffer left?
			int nextBuffer = 0;
			for(; nextBuffer < _nrBuffers; nextBuffer++) {
				if (_buffers[nextBuffer] == 0) {
					break;
				}
			}
			if (nextBuffer < _nrBuffers) {
//				std::cout << "N";
				_buffers[nextBuffer] = (char*)malloc(_bufferSize);
				memcpy(_buffers[nextBuffer], buffer, _bufferSize);

				alBufferData(_bufferIds[nextBuffer], _format, _buffers[nextBuffer], _bufferSize, _freq);
				checkOpenALError(__LINE__);

				alSourceQueueBuffers(_alId, 1, &_bufferIds[nextBuffer]);
				checkOpenALError(__LINE__);
				// there was a free buffer, repoll immediately to try to write more
				if (repollAt)
					*repollAt = 0;

				break;
			} else {
//				std::cout << "X";
				// no processed, no new buffer, wait until we processed one
				if (blocking) {
					tthread::this_thread::sleep_for(tthread::chrono::milliseconds(_repollSleep));
				} else {
					if (repollAt)
						*repollAt = _repollSleep;
					return -1;
				}
			}
		}
	}

	// we have at least one buffer queued, start playing
	if (!_isStarted || !isPlaying()) {
		alSourcePlay(_alId);
		checkOpenALError(__LINE__);
		_isStarted = true;
	}

	return size;
}


/**
* Dequeue, refill and re-enqueue buffers.
*/
void OpenALPlayer::updateBuffers() {
	int processed;
//  int queued;

//  std::cout << "Initial sleep: " << initialSleep << "ms" << std::endl;
//  std::cout << "Buffer sleep: " << bufferSleep << "ms" << std::endl;
//  std::cout << "Repoll sleep: " << repollSleep << "ms" << std::endl;
	tthread::this_thread::sleep_for(tthread::chrono::milliseconds(_bufferSleep * _initialSleep));


	while(_isStarted) {

		// how many buffers have been rendered already?
		tthread::lock_guard<tthread::recursive_mutex> lock(_alMutex);
		alGetSourcei(_alId, AL_BUFFERS_PROCESSED, &processed);
		checkOpenALError(__LINE__);
		//std::cout << processed << std::flush;

		if (processed == 0) {
			// avoid busy wait by sleeping
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(_bufferSleep * _initialSleep));
		} else {
			// dequeue buffers and get ids
			// see http://stackoverflow.com/questions/1900665/c-compiler-differences-vs2008-and-g
			ALuint bufferIds[ALPLAY_NR_AUDIO_BUFFERS];
			alSourceUnqueueBuffers(_alId, processed, bufferIds);
			checkOpenALError(__LINE__);

			for (int id = 0; id < processed; id++) {
				int bufferIdx = bufferIndex(bufferIds[id]);

				// refill the buffer with data from the callback
				_audioCallback->getSamples(_buffers[bufferIdx], _bufferSize, this);
				alBufferData(bufferIds[id], _format, _buffers[bufferIdx], _bufferSize, _freq);
				checkOpenALError(__LINE__);

			}
			// re-enqueue
			alSourceQueueBuffers(_alId, processed, bufferIds);
			checkOpenALError(__LINE__);

			// restart if we are not running anymore
			if (!isPlaying()) {
				alSourcePlay(_alId);
				checkOpenALError(__LINE__);
			}

			// sleep a bit less than the duration of one buffer
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(_bufferSleep * processed));
		}
	}
}

/**
* TODO
*/
void OpenALPlayer::stop() {
	_isStarted = false;
	_thread->join();
}

void OpenALPlayer::checkOpenALError(int line) {
	int error = alGetError();
	if(error != AL_NO_ERROR) {
		std::stringstream out;
		out << "OpenALError:" << line << ":";

		switch (error) {
		case AL_INVALID_NAME:
			out << "OpenAL invalid name.";
			break;
		case AL_INVALID_ENUM:
			out << "OpenAL invalid enum.";
			break;
		case AL_INVALID_VALUE:
			out << "OpenAL invalid value.";
			break;
		case AL_INVALID_OPERATION:
			out << "OpenAL invalid operation.";
			break;
		case AL_OUT_OF_MEMORY:
			out << "OpenAL out of memory.";
			break;

		default:
			out << "OpenAL unknown error.";
			break;
		}
		throw std::runtime_error(out.str());
	}
}

unsigned int OpenALPlayer::isPlaying() {
	ALint val;
	alGetSourcei(_alId, AL_SOURCE_STATE, &val);
	if(val != AL_PLAYING)
		return 0;
	return _repollSleep;
}

void OpenALPlayer::updateBuffersWrapper(void *obj) {
	try {
		reinterpret_cast<OpenALPlayer *>(obj)->updateBuffers();
	} catch(std::runtime_error& error) {
//		std::cout << "Terminating Thread: " << error << std::endl;
	} catch(...) {
//		std::cout << "Terminating Thread! " << std::endl;
	}
}

void OpenALPlayer::setNrBuffers(int nrBuffers) {
	if (_nrBuffers > 0)
		throw std::runtime_error("cannot modify number of buffers");
	_nrBuffers = nrBuffers;
}

int OpenALPlayer::getNrBuffers() {
	return _nrBuffers;
}

/**
* Set position of sound source in coordinate system
*/
void OpenALPlayer::setPosition(ALfloat position[]) {
	memcpy(&_position, position, 3 * sizeof(ALfloat));
//  std::cout << _position[0] << ", " << _position[1] << ", " << _position[2] << std::endl;
	if (_isInitialized)
		alSourcefv(_alId, AL_POSITION, _position);
}

ALfloat* OpenALPlayer::getPosition() {
	return _position;
}

/**
* Set velocity of sound source in coordinate system
*/
void OpenALPlayer::setVelocity(ALfloat velocity[]) {
	memcpy(&_velocity, velocity, 3 * sizeof(ALfloat));
	if (_isInitialized)
		alSourcefv(_alId, AL_VELOCITY, _velocity);
}

ALfloat* OpenALPlayer::getVelocity() {
	return _velocity;
}

/**
* Set direction of sound source in coordinate system
*/
void OpenALPlayer::setDirection(ALfloat direction[]) {
	memcpy(&_direction, direction, 3 * sizeof(ALfloat));
	if (_isInitialized)
		alSourcefv(_alId, AL_DIRECTION, _direction);
}

ALfloat* OpenALPlayer::getDirection() {
	return _direction;
}

void OpenALPlayer::setBufferSize(int bufferSize) {
	if (_bufferSize > 0)
		throw std::runtime_error("cannot modify buffersize");
	_bufferSize = bufferSize;
}

int OpenALPlayer::getBufferSize() {
	return _bufferSize;
}

OpenALPlayerCallback* OpenALPlayer::getCallback() {
	return _audioCallback;
}
void OpenALPlayer::setCallback(OpenALPlayerCallback* callback) {
	_audioCallback = callback;
}

void* OpenALPlayer::getUserData() {
	return _userData;
}
void OpenALPlayer::setUserData(void* userData) {
	_userData = userData;
}
