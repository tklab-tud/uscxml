#include "LibSoundFile.h"

namespace uscxml {

LibSoundFile::LibSoundFile(const std::string filename) : PCMConverter() {
	_filename = filename;
	_handle = SndfileHandle(_filename, SFM_READ, SF_FORMAT_PCM_16, 1, 44100);
	_format.sampleRate = _handle.samplerate();
	_format.alFormat = AL_FORMAT_MONO16;
	
}

LibSoundFile::~LibSoundFile() {
  
}

void LibSoundFile::seek(unsigned int pos) {
  _handle.seek(pos, 0);
}

int LibSoundFile::read(char* buffer, unsigned int size) {
  return _handle.readRaw(buffer, size);
}
 
void LibSoundFile::setOutFormat(const PCMFormat& format) {
	_format = format;
	switch (_format.alFormat) {
		case AL_FORMAT_MONO8:
			_handle = SndfileHandle(_filename, SFM_READ, SF_FORMAT_PCM_S8, 1, _format.sampleRate);
			break;
		case AL_FORMAT_MONO16:
			_handle = SndfileHandle(_filename, SFM_READ, SF_FORMAT_PCM_16, 1, _format.sampleRate);
			break;
		case AL_FORMAT_STEREO8:
			_handle = SndfileHandle(_filename, SFM_READ, SF_FORMAT_PCM_S8, 2, _format.sampleRate);
			break;
		case AL_FORMAT_STEREO16:
			_handle = SndfileHandle(_filename, SFM_READ, SF_FORMAT_PCM_16, 2, _format.sampleRate);
			break;
			
		default:
			break;
	}
}

PCMFormat LibSoundFile::getInFormat() {
	return _format;
}

}