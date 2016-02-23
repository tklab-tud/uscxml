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

#include <boost/algorithm/string.hpp>

#include "FetchElement.h"
#include "uscxml/dom/DOMUtils.h"
#include <glog/logging.h>

#include <event2/http.h>
#include <event2/http_struct.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new FetchElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> FetchElement::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<FetchElement> element = boost::shared_ptr<FetchElement>(new FetchElement());
	element->_interpreter = interpreter;
	return element;
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
	} else if (iequals(_type, "text")) {
		event.data.atom = content;
		event.data.type = Data::VERBATIM;
	} else if (iequals(_type, "url")) {
	} else if (iequals(_type, "json")) {
		event.data = Data::fromJSON(content);
	} else if (iequals(_type, "xml")) {
		event = Event::fromXML(content);
	}

	_interpreter->receive(event);

}

void FetchElement::downloadFailed(const URL& url, int errorCode) {
	Event event;
	event.name = _callback + ".failed";

	_interpreter->receive(event);

}

void FetchElement::enterElement(const Arabica::DOM::Element<std::string>& node) {
	if (!HAS_ATTR(node, "src") && !HAS_ATTR(node, "srcexpr")) {
		LOG(ERROR) << "Fetch element requires src or srcexpr";
		return;
	}
	if (HAS_ATTR(node, "srcexpr") && !_interpreter->getDataModel()) {
		LOG(ERROR) << "Fetch element with srcexpr requires datamodel";
		return;
	}
	_source = (HAS_ATTR(node, "src") ? ATTR(node, "src") : _interpreter->getDataModel().evalAsString(ATTR(node, "srcexpr")));

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
	if (!iequals(_type, "text") &&
	        !iequals(_type, "url") &&
	        !iequals(_type, "json") &&
	        !iequals(_type, "xml")) {
		LOG(ERROR) << "Fetch element type attribute not one of text, url, json, xml.";
		return;
	}

	_targetUrl = URL(_source);
	if (!_targetUrl.isAbsolute()) {
		if (!_targetUrl.toAbsolute(_interpreter->getBaseURL(node))) {
			LOG(ERROR) << "Cannot transform " << _source << " into absolute URL";
			return;
		}
	}

	_targetUrl.addMonitor(this);
	URLFetcher::fetchURL(_targetUrl);

}

void FetchElement::exitElement(const Arabica::DOM::Element<std::string>& node) {

}

}