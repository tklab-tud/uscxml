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

#ifndef UUID_H_8X65R2EI
#define UUID_H_8X65R2EI

#include "uscxml/Common.h"
#include <string>

namespace uscxml {

class USCXML_API UUID {
public:
	static std::string getUUID();
	static bool isUUID(const std::string& uuid);
};

}


#endif /* end of include guard: UUID_H_8X65R2EI */
