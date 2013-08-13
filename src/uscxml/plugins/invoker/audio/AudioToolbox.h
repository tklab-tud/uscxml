#ifndef AUDIOTOOLBOX_H_GX4SW17C
#define AUDIOTOOLBOX_H_GX4SW17C

#include "PCMConverter.h"
#include <AudioToolbox/AudioToolbox.h>

namespace uscxml {

class AudioToolbox : public PCMConverter {
public:
	AudioToolbox(const std::string filename);
	virtual ~AudioToolbox();
	virtual void seek(unsigned int pos);
	virtual int read(char* buffer, unsigned int size);

	virtual void setOutFormat(const PCMFormat& format);
	virtual PCMFormat getInFormat();

protected:
	ExtAudioFileRef _afId;
	AudioStreamBasicDescription	_outputFormat;
	AudioStreamBasicDescription _inputFormat;

	ALenum formatToALEnum(AudioStreamBasicDescription);
	bool alEnumToFormat(AudioStreamBasicDescription&, ALenum);
};

}

#endif /* end of include guard: AUDIOTOOLBOX_H_GX4SW17C */


