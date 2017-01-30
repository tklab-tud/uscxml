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

#ifndef SHA1_HPP_XJADWV5G
#define SHA1_HPP_XJADWV5G

extern "C" {
#include "SHA1.h"
}

#include <string.h>
#include <sstream>
#include <iomanip>
#include "uscxml/Common.h"

namespace uscxml {
    USCXML_API inline std::string sha1(const char* data, size_t length) {
        SHA1Context sha;
        SHA1Reset(&sha);
        SHA1Input(&sha, (const unsigned char*)data, length);
        if (!SHA1Result(&sha)) {
            return "";
        } else {
        	std::ostringstream ss;
        	ss << std::hex << std::uppercase << std::setfill( '0' );
        	for (size_t i = 0; i < 5; i++) {
        		ss << std::setw( 2 ) << sha.Message_Digest[i];
        	}

        	return ss.str();
        }
    }

    USCXML_API inline std::string sha1(const std::string& data) {
    	return sha1(data.data(), data.size());
    }
}

#endif /* end of include guard: SHA1_HPP_XJADWV5G */
