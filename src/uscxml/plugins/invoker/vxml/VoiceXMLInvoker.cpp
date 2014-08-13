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

#include "VoiceXMLInvoker.h"
#include <glog/logging.h>
#include "uscxml/UUID.h"

#include <DOM/io/Stream.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define ISSUE_REQUEST(name) {\
	Arabica::DOM::Document<std::string> name##XML = name.toXML(true);\
	name##XML.getDocumentElement().setPrefix("mmi");\
	std::stringstream name##XMLSS;\
	name##XMLSS << name##XML;\
	URL name##URL(target);\
	name##URL.setOutContent(name##XMLSS.str());\
	name##URL.addOutHeader("Content-type", "application/xml");\
	name##URL.download(false);\
}

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new VoiceXMLInvokerProvider() );
	return true;
}
#endif

VoiceXMLInvoker::VoiceXMLInvoker() {
}

VoiceXMLInvoker::~VoiceXMLInvoker() {
};

boost::shared_ptr<InvokerImpl> VoiceXMLInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<VoiceXMLInvoker> invoker = boost::shared_ptr<VoiceXMLInvoker>(new VoiceXMLInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

bool VoiceXMLInvoker::httpRecvRequest(const HTTPServer::Request& request) {
	return true;
}

void VoiceXMLInvoker::setURL(const std::string& url) {
	_url = url;
}

Data VoiceXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void VoiceXMLInvoker::send(const SendRequest& req) {
}

void VoiceXMLInvoker::invoke(const InvokeRequest& req) {
	HTTPServer::getInstance()->registerServlet(req.invokeid, this);
	
	std::string target;
	Event::getParam(req.params, "target", target);
	
	NewContextRequest newCtxReq;
	newCtxReq.source = _url;
	newCtxReq.target = target;
	newCtxReq.requestId = uscxml::UUID::getUUID();
	ISSUE_REQUEST(newCtxReq);

	_isRunning = true;
	_thread = new tthread::thread(VoiceXMLInvoker::run, this);

}

void VoiceXMLInvoker::run(void* instance) {
	VoiceXMLInvoker* INSTANCE = (VoiceXMLInvoker*)instance;
	while(true) {
		SendRequest req = INSTANCE->_workQueue.pop();
		if (INSTANCE->_isRunning) {
			INSTANCE->process(req);
		} else {
			return;
		}
	}
}

void VoiceXMLInvoker::process(SendRequest& ctx) {
	
}
	
void VoiceXMLInvoker::uninvoke() {
	HTTPServer::getInstance()->unregisterServlet(this);
}

}