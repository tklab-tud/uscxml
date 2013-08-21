#ifndef OPENALPLAYER_H_3PORVJDU
#define OPENALPLAYER_H_3PORVJDU

#include <iostream>
#include <string.h>
#include <stdlib.h>
#include <sstream>
#include <uscxml/concurrency/tinythread.h>

#include <al.h>
#include <alc.h>

// sometimes the stream drops if this is less than 5000 bytes
#define ALPLAY_NR_AUDIO_BUFFERS 3
#define ALPLAY_AUDIO_BUFFER_SIZE 2048
//#define ALPLAYER_FORMAT_MONO16 0x1101

class OpenALPlayer;

class OpenALPlayerCallback {
public:
	virtual ~OpenALPlayerCallback() {}
	/*
	* Returning an OpenALPlayerCallback is a hack to be able to provide a typemap for SWIG.
	* We cannot use SWIG directors with byte arrays otherwise. Posted to swig-ML already.
	*/
	virtual OpenALPlayerCallback* getSamples(char* buffer, int size, OpenALPlayer* player) = 0;
};

class OpenALPlayer {
private:
	ALCcontext* _context;

	ALuint _alId;
	ALfloat _position[3];
	ALfloat _velocity[3];
	ALfloat _direction[3];
	ALfloat _pitch;
	ALfloat _gain;
	ALfloat _referenceDistance;
	ALboolean _isLooping;

	// OpenAL is not really thread safe
	static tthread::recursive_mutex _alMutex;

	ALenum _format;
	ALsizei _freq;
	int _msForBuffer;
	int _initialSleep;
	int _bufferSleep;
	int _repollSleep;

	int _bufferSize;
	int _nrBuffers;
	ALuint* _bufferIds;
	char** _buffers;
	OpenALPlayerCallback* _audioCallback;
	void* _userData;

	tthread::thread* _thread;
	bool _isStarted;
	bool _isInitialized;

	void updateBuffers();
	void init();

	// static wrapper as an entry point for pthreads
	static void updateBuffersWrapper(void *obj);

	// get the index in _buffers for a buffer ID
	int inline bufferIndex(int bufferId);

public:
	OpenALPlayer(ALCcontext*, OpenALPlayerCallback*, ALenum, ALsizei);
	virtual ~OpenALPlayer();

	unsigned int isPlaying();
	static void checkOpenALError(int line);

	ALfloat* getPosition();
	void setPosition(ALfloat[3]);
	ALfloat* getVelocity();
	void setVelocity(ALfloat[3]);
	ALfloat* getDirection();
	void setDirection(ALfloat[3]);

	void setBufferSize(int bufferSize);
	int getBufferSize();
	void setNrBuffers(int nrBuffers);
	int getNrBuffers();

	// callback interface for pull
	OpenALPlayerCallback* getCallback();
	void setCallback(OpenALPlayerCallback* callback);

	// stream interface for push
	int write(char* buffer, int size, int* repollAt, bool blocking = false);

	void* getUserData();
	void setUserData(void* userData);

	void start();
	void stop();
};

#endif /* end of include guard: OPENALPLAYER_H_3PORVJDU */
