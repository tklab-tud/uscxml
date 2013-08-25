#include "VoiceXMLInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
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