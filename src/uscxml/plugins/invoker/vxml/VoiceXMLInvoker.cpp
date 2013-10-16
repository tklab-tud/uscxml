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

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

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
	invoker->_pub = umundo::TypedPublisher("mmi:jvoicexml");
	invoker->_sub = umundo::TypedSubscriber("mmi:jvoicexml");

	invoker->_pub.registerType("LifeCycleEvent", new ::LifeCycleEvent());


	invoker->_node.addPublisher(invoker->_pub);
	invoker->_node.addSubscriber(invoker->_sub);

	return invoker;
}

void VoiceXMLInvoker::receive(void* object, umundo::Message* msg) {
	std::cout << msg->getMeta("um.s11n.type") << std::endl;
}

Data VoiceXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void VoiceXMLInvoker::send(const SendRequest& req) {
	StartRequest start;
	std::stringstream domSS;
//	if (req.dom) {
//		// hack until jVoiceXML supports XML
//		std::cout << req.dom;
//		Arabica::DOM::NodeList<std::string> prompts = req.dom.getElementsByTagName("vxml:prompt");
//		for (int i = 0; i < prompts.getLength(); i++) {
//			if (prompts.item(i).hasChildNodes()) {
//				domSS << prompts.item(i).getFirstChild().getNodeValue() << ".";
//			}
//		}
//	}
//	domSS << req.getFirstDOMElement();
	domSS << req.dom;
	start.content = domSS.str();
	_interpreter->getDataModel().replaceExpressions(start.content);

	start.requestId = "asdf";
	start.source = "asdf";
	start.target = "umundo://mmi/jvoicexml";
	::LifeCycleEvent lce = MMIProtoBridge::toProto(start);
	_pub.sendObj("LifeCycleEvent", &lce);
}

void VoiceXMLInvoker::invoke(const InvokeRequest& req) {
	_pub.waitForSubscribers(1);

}

}