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

#include "AudioToolbox.h"
#include <glog/logging.h>

#import <Foundation/Foundation.h>
#import <Foundation/NSURL.h>

#ifdef __has_feature
# if __has_feature(objc_arc)
#   define(HAS_AUTORELEASE_POOL)
# endif
#endif

namespace uscxml {

AudioToolbox::AudioToolbox(const std::string filename) {
#if HAS_AUTORELEASE_POOL
  @autoreleasepool {
#else
  NSAutoreleasePool *pool = [[NSAutoreleasePool alloc] init];
#endif
		_afId = 0;
		NSString* filePath = [NSString stringWithCString:filename.c_str() encoding:NSASCIIStringEncoding];
		NSURL* afUrl = [NSURL fileURLWithPath:filePath];

		OSStatus result = noErr;
		
		result = ExtAudioFileOpenURL((CFURLRef)afUrl, &_afId);

		if (result != noErr) {
			LOG(WARNING) << "Cannot open audio file " << filename;
			return;
		}
		UInt32 thePropertySize = sizeof(_inputFormat);
		result = ExtAudioFileGetProperty(_afId, kExtAudioFileProperty_FileDataFormat, &thePropertySize, &_inputFormat);
		if (result != noErr) {
			LOG(WARNING) << "Cannot determine input format of " << filename;
			return;
		}

		// output format is input format
		memcpy(&_outputFormat, &_inputFormat, sizeof(_inputFormat));

		// except for things that make no sense for open al
		_outputFormat.mFormatID = kAudioFormatLinearPCM;
		_outputFormat.mFormatFlags = kAudioFormatFlagsNativeEndian | kAudioFormatFlagIsPacked | kAudioFormatFlagIsSignedInteger;

		ALenum bestFormat = formatToALEnum(_outputFormat);
		alEnumToFormat(_outputFormat, bestFormat);
		
		result = ExtAudioFileSetProperty(_afId, kExtAudioFileProperty_ClientDataFormat, sizeof(_outputFormat), &_outputFormat);

		if (result != noErr) {
			LOG(WARNING) << "Cannot set audio format file " << filename;
			return;
		}

#if HAS_AUTORELEASE_POOL
  }
#else
  [pool drain];
#endif
}

AudioToolbox::~AudioToolbox() {
  if (_afId)
		ExtAudioFileDispose(_afId); //close the file
}

void AudioToolbox::seek(unsigned int pos) {
	ExtAudioFileSeek(_afId, pos);
}

int AudioToolbox::read(char* buffer, unsigned int size) {
	UInt32 read = size / _outputFormat.mBytesPerFrame;
  OSStatus result = noErr;
	
	SInt64 theFileLengthInFrames = 0;
	UInt32 thePropertySize = sizeof(theFileLengthInFrames);
	result = ExtAudioFileGetProperty(_afId, kExtAudioFileProperty_FileLengthFrames, &thePropertySize, &theFileLengthInFrames);

	read = (theFileLengthInFrames < read ? theFileLengthInFrames : read);
	
	AudioBufferList dataBuffer;
	dataBuffer.mNumberBuffers = 1;
	dataBuffer.mBuffers[0].mDataByteSize = size;
	dataBuffer.mBuffers[0].mNumberChannels = _outputFormat.mChannelsPerFrame;
	dataBuffer.mBuffers[0].mData = buffer;

	result = ExtAudioFileRead(_afId, &read, &dataBuffer);
	if (result != noErr) {
		LOG(WARNING) << "Cannot read data";
		return 0;
	}

	return read * _outputFormat.mBytesPerFrame;
}

ALenum AudioToolbox::formatToALEnum(AudioStreamBasicDescription asbd) {
	if (asbd.mBitsPerChannel < 16) {
		if (asbd.mChannelsPerFrame == 1) {
			return AL_FORMAT_MONO8;
		} else {
			return AL_FORMAT_STEREO8;
		}
	} else {
		if (asbd.mChannelsPerFrame == 1) {
			return AL_FORMAT_MONO16;
		} else {
			return AL_FORMAT_STEREO16;
		}	
	}
}
	
bool AudioToolbox::alEnumToFormat(AudioStreamBasicDescription& asbd, ALenum format) {
	switch (format) {
		case AL_FORMAT_MONO8:
			asbd.mBitsPerChannel = 8;
			asbd.mBytesPerFrame = 1;
			asbd.mBytesPerPacket = 1;
			asbd.mChannelsPerFrame = 1;
			break;
		case AL_FORMAT_MONO16:
			asbd.mBitsPerChannel = 16;
			asbd.mBytesPerFrame = 2;
			asbd.mBytesPerPacket = 2;
			asbd.mChannelsPerFrame = 1;
			break;
		case AL_FORMAT_STEREO8:
			asbd.mBitsPerChannel = 8;
			asbd.mBytesPerFrame = 2;
			asbd.mBytesPerPacket = 2;
			asbd.mChannelsPerFrame = 2;
			break;
		case AL_FORMAT_STEREO16:
			asbd.mBitsPerChannel = 16;
			asbd.mBytesPerFrame = 4;
			asbd.mBytesPerPacket = 4;
			asbd.mChannelsPerFrame = 2;
			break;
		default:
			break;
	}
	return true;
}

void AudioToolbox::setOutFormat(const PCMFormat& format) {
	
	alEnumToFormat(_outputFormat, format.alFormat);
	_outputFormat.mSampleRate = format.sampleRate;

	OSStatus result = ExtAudioFileSetProperty(_afId, kExtAudioFileProperty_ClientDataFormat, sizeof(_outputFormat), &_outputFormat);
	if (result != noErr) {
		LOG(WARNING) << "Cannot set audio format";
		return;
	}

}

PCMFormat AudioToolbox::getInFormat() {
	PCMFormat format;
	format.sampleRate = _inputFormat.mSampleRate;
	format.alFormat = formatToALEnum(_inputFormat);
	return format;
}

}