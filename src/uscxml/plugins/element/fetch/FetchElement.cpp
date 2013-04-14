#include "FetchElement.h"
#include <glog/logging.h>

#include <event2/http.h>
#include <event2/http_struct.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new FetchElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> FetchElement::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<FetchElement> invoker = boost::shared_ptr<FetchElement>(new FetchElement());
	invoker->_interpreter = interpreter;
	return invoker;
}

FetchElement::~FetchElement() {
	URLFetcher::breakURL(_targetUrl);
}

void FetchElement::downloadCompleted(const URL& url) {
	Event event;
	event.name = _callback;

	std::string content = url.getInContent();
	std::map<std::string, std::string> headerFields = url.getInHeaderFields();

	if (false) {
	} else if (boost::iequals(_type, "text")) {
		event.data.atom = content;
		event.data.type = Data::VERBATIM;
	} else if (boost::iequals(_type, "url")) {
	} else if (boost::iequals(_type, "json")) {
		event.data = Data::fromJSON(content);
	} else if (boost::iequals(_type, "xml")) {
		event = Event::fromXML(content);
	}

	_interpreter->receive(event);

}

void FetchElement::downloadFailed(const URL& url, int errorCode) {
	Event event;
	event.name = _callback + ".failed";

	_interpreter->receive(event);

}

void FetchElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
	if (!HAS_ATTR(node, "target") && !HAS_ATTR(node, "targetexpr")) {
		LOG(ERROR) << "Fetch element requires target or targetexpr";
		return;
	}
	if (HAS_ATTR(node, "targetexpr") && !_interpreter->getDataModel()) {
		LOG(ERROR) << "Fetch element with targetexpr requires datamodel";
		return;
	}
	_target = (HAS_ATTR(node, "target") ? ATTR(node, "target") : _interpreter->getDataModel().evalAsString(ATTR(node, "targetexpr")));

	if (!HAS_ATTR(node, "callback") && !HAS_ATTR(node, "callbackexpr")) {
		LOG(ERROR) << "Fetch element requires callback or callbackexpr";
		return;
	}
	if (HAS_ATTR(node, "callbackexpr") && !_interpreter->getDataModel()) {
		LOG(ERROR) << "Fetch element with callbackexpr requires datamodel";
		return;
	}
	_callback = (HAS_ATTR(node, "callback") ? ATTR(node, "callback") : _interpreter->getDataModel().evalAsString(ATTR(node, "callbackexpr")));

	_type = (HAS_ATTR(node, "type") ? ATTR(node, "type") : "text");
	if (!boost::iequals(_type, "text") &&
	        !boost::iequals(_type, "url") &&
	        !boost::iequals(_type, "json") &&
	        !boost::iequals(_type, "xml")) {
		LOG(ERROR) << "Fetch element type attribute not one of text, url, json, xml.";
		return;
	}

	_targetUrl = URL(_target);
	if (!_targetUrl.isAbsolute()) {
		if (!_targetUrl.toAbsolute(_interpreter->getBaseURI())) {
			LOG(ERROR) << "Cannot transform " << _target << " into absolute URL";
			return;
		}
	}

	_targetUrl.addMonitor(this);
	URLFetcher::fetchURL(_targetUrl);

}

void FetchElement::exitElement(const Arabica::DOM::Node<std::string>& node) {

}

}