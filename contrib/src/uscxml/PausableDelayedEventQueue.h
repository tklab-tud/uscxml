/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef PAUSABLEDELAYEDEVENTQUEUE_H_F26D6161
#define PAUSABLEDELAYEDEVENTQUEUE_H_F26D6161

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"

#include <memory>

namespace uscxml {

/**
 * A DelayedEventQueue that implements pause/resume
 * @ingroup eventqueue
 * @ingroup impl
 */
class USCXML_API PausableDelayedEventQueue : public BasicDelayedEventQueue {
public:
	PausableDelayedEventQueue(DelayedEventQueueCallbacks* callbacks);
	std::shared_ptr<DelayedEventQueueImpl> create(DelayedEventQueueCallbacks* callbacks);

	void pause();
	void resume();
	
protected:
	timeval _pausedAt;
};

}



#endif /* end of include guard: PAUSABLEDELAYEDEVENTQUEUE_H_F26D6161 */
