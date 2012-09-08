#ifndef BLOCKINGQUEUE_H_4LEVMY0N
#define BLOCKINGQUEUE_H_4LEVMY0N

#include "uscxml/concurrency/tinythread.h"
#include <list>

namespace uscxml {
namespace concurrency {

template <class T>
class BlockingQueue {
public:
	BlockingQueue() {}
	virtual ~BlockingQueue() {
  }

	void push(T elem) {
    tthread::lock_guard<tthread::mutex> lock(_mutex);
    _queue.push_back(elem);
    _cond.notify_all();
  }
  
	T pop() {
    tthread::lock_guard<tthread::mutex> lock(_mutex);
    while (_queue.empty()) {
      _cond.wait(_mutex);
    }
    T ret = _queue.front();
    _queue.pop_front();
    return ret;
  }

	tthread::mutex _mutex;
  tthread::condition_variable _cond;
	std::list<T> _queue;
};

}
}

#endif /* end of include guard: BLOCKINGQUEUE_H_4LEVMY0N */
