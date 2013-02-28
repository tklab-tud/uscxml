#include "PostponeElement.h"
#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new PostponeElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> PostponeElement::create(Interpreter* interpreter) {
	boost::shared_ptr<PostponeElement> invoker = boost::shared_ptr<PostponeElement>(new PostponeElement());
	invoker->_interpreter = interpreter;
	return invoker;
}

void PostponeElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
	if (!_interpreter->getDataModel()) {
		LOG(ERROR) << "Postpone element requires a datamodel";
		return;
	}

	// under which condition will we postpone the current event?
	if (HAS_ATTR(node, "cond")) {
		std::string cond = ATTR(node, "cond");
		try {
			if (!_interpreter->getDataModel().evalAsBool(cond))
				return;
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in cond attribute of postpone element:" << std::endl << e << std::endl;
			return;
		}
	}

	// when will we refire the event?
  std::string until;
  try {
    if (HAS_ATTR(node, "untilexpr")) {
      until = _interpreter->getDataModel().evalAsString(ATTR(node, "untilexpr"));
    } else if (HAS_ATTR(node, "until")) {
      until = ATTR(node, "until");
    }
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in postpone element untilexpr:" << std::endl << e << std::endl;
    return;
	}

	if (until.length() == 0) {
		LOG(ERROR) << "Postpone element requires until or untilexpr attribute ";
		return;
	}

	Event currEvent = _interpreter->getCurrentEvent();
	Resubmitter::postpone(currEvent, until, _interpreter);
}

void PostponeElement::exitElement(const Arabica::DOM::Node<std::string>& node) {
}

void PostponeElement::Resubmitter::postpone(const Event& event, std::string until, Interpreter* interpreter) {
	Resubmitter* resubmitter = getInstance(interpreter);
	resubmitter->_postponedEvents.push_back(std::make_pair(until, event));
}

void PostponeElement::Resubmitter::onStableConfiguration(Interpreter* interpreter) {
	std::list<std::pair<std::string, Event> >::iterator eventIter = _postponedEvents.begin();
	while(eventIter != _postponedEvents.end()) {
		try {
      LOG(INFO) << "Reevaluating: >> " << eventIter->first << " <<";
			if (interpreter->getDataModel().evalAsBool(eventIter->first)) {
        LOG(INFO) << "  -> is TRUE";
				interpreter->receive(eventIter->second, true);
				_postponedEvents.erase(eventIter);
				break;
			}
      LOG(INFO) << "  -> is FALSE";
		} catch (Event e) {
			LOG(ERROR) << "Syntax error while evaluating until attribute of postpone element:" << std::endl << e << std::endl;
			_postponedEvents.erase(eventIter++);
			continue;
		}
		eventIter++;
	}
}

void PostponeElement::Resubmitter::afterCompletion(Interpreter* interpreter) {
	tthread::lock_guard<tthread::recursive_mutex> lock(PostponeElement::Resubmitter::_accessLock);
	_instances.erase(interpreter);
	delete this; // committing suicide is ok if we are careful
}

std::map<Interpreter*, PostponeElement::Resubmitter*> PostponeElement::Resubmitter::_instances;
tthread::recursive_mutex PostponeElement::Resubmitter::_accessLock;

PostponeElement::Resubmitter* PostponeElement::Resubmitter::getInstance(Interpreter* interpreter) {
	tthread::lock_guard<tthread::recursive_mutex> lock(PostponeElement::Resubmitter::_accessLock);
	if (_instances.find(interpreter) == _instances.end()) {
		_instances[interpreter] = new Resubmitter(interpreter);
	}
	return _instances[interpreter];
}

}