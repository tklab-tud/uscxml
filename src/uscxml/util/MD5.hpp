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

#ifndef MD5_HPP_70TU4G5T
#define MD5_HPP_70TU4G5T

extern "C" {
#include "MD5.h"
}

#include <string.h>

#include <sstream>
#include <iomanip>
#include "uscxml/Common.h"

namespace uscxml {

    USCXML_API inline std::string md5(const char* data, size_t length) {
    	md5_state_t state;
    	md5_byte_t digest[16];

    	md5_init(&state);
    	md5_append(&state, (const md5_byte_t *)data, length);
    	md5_finish(&state, digest);

    	std::ostringstream ss;
    	ss << std::hex << std::uppercase << std::setfill( '0' );
    	for (size_t i = 0; i < 16; i++) {
    		ss << std::setw( 2 ) << (int)digest[i];
    	}

    	return ss.str();
    }

    USCXML_API inline std::string md5(const std::string& data) {
    	return md5(data.data(), data.size());
    }

}


#endif /* end of include guard: MD5_HPP_70TU4G5T */
