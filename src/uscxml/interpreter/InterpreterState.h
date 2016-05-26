/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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


#ifndef INTERPRETERSTATE_H_E6CCAEA5
#define INTERPRETERSTATE_H_E6CCAEA5


#include "uscxml/Common.h"

namespace uscxml {

enum InterpreterState {
	USCXML_FINISHED       = -1,  ///< machine reached a final configuration and is done
	USCXML_UNDEF          = 0,   ///< not an actual state
	USCXML_IDLE           = 1,   ///< stable configuration and queues empty
	USCXML_INITIALIZED    = 2,   ///< DOM is setup and all external components instantiated
	USCXML_INSTANTIATED   = 3,   ///< nothing really, just instantiated
	USCXML_MICROSTEPPED   = 4,   ///< processed one transition set
	USCXML_MACROSTEPPED   = 5,   ///< processed all transition sets and reached a stable configuration
	USCXML_CANCELLED      = 6,   ///< machine was cancelled, step once more to finalize
};


}

#endif /* end of include guard: INTERPRETERSTATE_H_E6CCAEA5 */
