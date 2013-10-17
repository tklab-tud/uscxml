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

#ifndef LIBSOUNDFILE_H_Q97OEKGG
#define LIBSOUNDFILE_H_Q97OEKGG

#include "PCMConverter.h"
#include <sndfile.hh>

namespace uscxml {

class LibSoundFile : public PCMConverter {
public:
	LibSoundFile(const std::string filename);
	virtual ~LibSoundFile();
	void seek(unsigned int pos);
	int read(char* buffer, unsigned int size);

	virtual void setOutFormat(const PCMFormat& format);
	virtual PCMFormat getInFormat();

protected:
	std::string _filename;
	SndfileHandle _handle;
	PCMFormat _format;
};

}

#endif /* end of include guard: LIBSOUNDFILE_H_Q97OEKGG */
