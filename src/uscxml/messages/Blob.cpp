/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/messages/Blob.h"

#include "uscxml/util/MD5.hpp"
#include "uscxml/util/Base64.hpp"

namespace uscxml {

Blob::~Blob() {
	free(data);
}

std::string Blob::md5() {
	return uscxml::md5(data, size);
}

Blob* Blob::fromBase64(const std::string base64) {
	std::string decoded = base64Decode(base64);
	return new Blob((void*)decoded.c_str(), decoded.length(), mimeType);
}

Blob::Blob(size_t _size) {
	data = (char*)malloc(_size);
	memset(data, 0, _size);
	size = _size;
}

Blob::Blob(void* _data, size_t _size, const std::string& _mimeType, bool adopt) {
	if (adopt) {
		data = (char*)_data;
	} else {
		data = (char*)malloc(_size);
		memcpy(data, _data, _size);
	}
	mimeType = _mimeType;
	size = _size;
}

std::string Blob::base64() {
	return base64Encode((char* const)data, size);
}

}