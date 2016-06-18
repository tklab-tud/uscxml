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

#ifndef BLOCKINGQUEUE_H_4LEVMY0N
#define BLOCKINGQUEUE_H_4LEVMY0N

#include "uscxml/Common.h"
#include <list>
#include <condition_variable>

namespace uscxml {

template <class T>
class BlockingQueue {
public:
	BlockingQueue() {}
	virtual ~BlockingQueue() {
	}

	virtual void push(const T& elem) {
		std::lock_guard<std::mutex> lock(_mutex);
		_queue.push_back(elem);
		_cond.notify_all();
	}

	virtual void push_front(const T& elem) {
		std::lock_guard<std::mutex> lock(_mutex);
		_queue.push_front(elem);
		_cond.notify_all();
	}

	virtual T pop() {
		std::lock_guard<std::mutex> lock(_mutex);
//		std::cout << "Popping from " << this << std::endl;
		while (_queue.empty()) {
			_cond.wait(_mutex);
		}
		T ret = _queue.front();
		_queue.pop_front();
		return ret;
	}

	virtual void clear() {
		std::lock_guard<std::mutex> lock(_mutex);
		_queue.clear();
	}

	virtual bool isEmpty() {
		std::lock_guard<std::mutex> lock(_mutex);
		return _queue.empty();
	}

protected:
	std::mutex _mutex;
	std::condition_variable_any _cond;
	std::list<T> _queue;
};

}

#endif /* end of include guard: BLOCKINGQUEUE_H_4LEVMY0N */
