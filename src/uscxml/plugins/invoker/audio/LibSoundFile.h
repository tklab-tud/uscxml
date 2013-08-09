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
