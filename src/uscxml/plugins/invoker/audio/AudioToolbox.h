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


