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
