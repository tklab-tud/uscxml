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

#ifndef PCMCONVERTER_H_97Z8U7PA
#define PCMCONVERTER_H_97Z8U7PA

#include <string>
#include <al.h>
#include <alc.h>

namespace uscxml {

struct PCMFormat {
	ALenum alFormat;
	unsigned int sampleRate;
};

class PCMConverter {
public:
	PCMConverter(const std::string filename) {}
	virtual ~PCMConverter() {}
	virtual void seek(unsigned int pos) = 0;
	virtual int read(char* buffer, unsigned int size) = 0;

	virtual void setOutFormat(const PCMFormat& format) = 0;
	virtual PCMFormat getInFormat() = 0;
protected:
	PCMConverter() {}
};

}

#endif /* end of include guard: PCMCONVERTER_H_97Z8U7PA */
