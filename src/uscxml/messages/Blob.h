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

#ifndef BLOB_H_E1B6D2C3
#define BLOB_H_E1B6D2C3

#include <string>

#include "uscxml/Common.h"

namespace uscxml {

class USCXML_API Blob {
public:
	~Blob();
	Blob(size_t size);
	Blob(const char* data, size_t size, const std::string& mimeType, bool adopt = false);

	std::string base64();
	std::string md5();
	Blob* fromBase64(const std::string base64);
	
	char* getData() const {
		return data;
	}
	
	size_t getSize() const {
		return size;
	}
	
	std::string getMimeType() const {
		return mimeType;
	}
	
#ifdef SWIGIMPORTED
protected:
#endif

	char* data;
	size_t size;
	std::string mimeType;


};

}

#endif /* end of include guard: BLOB_H_E1B6D2C3 */
