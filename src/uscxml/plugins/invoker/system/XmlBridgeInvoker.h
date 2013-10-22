#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <map>
#include <iostream>

#include <uscxml/Interpreter.h>
#include <glog/logging.h>
#include "uscxml/plugins/invoker/system/timio.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

#define SCXML2TIM_EV	"cmd"
#define SCXML2MES_EV	"ack"
#define MES2SCXML_EV	"ready"
#define TIM2SCXML_EV	"reply"

class XmlBridgeInvoker : public InvokerImpl {
public:
	XmlBridgeInvoker() {}
	~XmlBridgeInvoker() {}

	std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);
	void send(const SendRequest& req);
	void invoke(const InvokeRequest& req);
	Data getDataModelVariables();

	void buildMESreq(unsigned int cmdid, const std::list<std::string> reply_raw_data);
	void buildTIMreply(const char cmdid, const std::string reply_raw_data);

protected:
	std::string _DBid;
};

class XmlBridgeInputEvents {
public:
	~XmlBridgeInputEvents();

	void sendreq2TIM(const char cmdid, const std::string reqData);
	void sendreply2MES(std::string DBid, const char cmdid, const std::string replyData);

	void handleTIMreply(const char cmdid, const std::string replyData);
	void handleMESreq(unsigned int DBid, unsigned int cmdid, const std::list<std::string> reqData);

	void registerInvoker(std::string DBid, XmlBridgeInvoker* invokref) {
		_invokers.insert(std::pair< std::string, XmlBridgeInvoker* >(DBid, invokref));
	}
	void registerTimio(TimIO* ioref) {
		_timio = ioref;
	}

	/** It is not the exact type since mesbufferer.h is included only in xmlbridgeinvoker.cpp */
	void registerMesbufferer(void* mesref) {
		_mesbufferer = mesref;
	}

	static XmlBridgeInputEvents& getInstance() {
		static XmlBridgeInputEvents instance;
		return instance;
	}

private:
	XmlBridgeInputEvents() : _invokers() {
		LOG(INFO) << "Instantiating XmlBridgeInputEvents Singleton";
	}
	XmlBridgeInputEvents& operator=( const XmlBridgeInputEvents& );

	/** One invoker/interpreter for each datablock */
	std::map<std::string, XmlBridgeInvoker*> _invokers;
	TimIO* _timio;

	/** It is not the exact type since mesbufferer.h is included only in xmlbridgeinvoker.cpp */
	void* _mesbufferer;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
