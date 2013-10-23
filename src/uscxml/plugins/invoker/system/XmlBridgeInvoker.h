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

#define SCXML2TIM_EV		"cmd"
#define SCXML2MES_EV		"ack"
#define MES2SCXML_READ		"read0"
#define MES2SCXML_WRITE		"write0"
#define TIM2SCXML_EV		"reply"
#define TIM2SCXML_TIMEOUT	"timeout"
#define TIM2SCXML_ERROR		"error"

#define INVOKER_TYPE		"xmlbridge"

enum exceptions {
	TIM_TIMEOUT,
	TIM_ERROR,
	SCXML_ERROR
};

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

	void buildMESreq(unsigned int cmdid, const std::list<std::string> req_raw_data);
	void buildTIMreply(unsigned int cmdid, const std::string reply_raw_data);
	void buildTIMexception(unsigned int cmdid, exceptions type);

protected:
	unsigned int _DBid;
	unsigned int _timeoutVal;
};

class XmlBridgeInputEvents {
public:
	~XmlBridgeInputEvents();

	void sendreq2TIM(const char *cmdid, const std::string reqData, unsigned int timeout);
	void sendreply2MES(unsigned int DBid, const char *cmdid, const std::string replyData);

	void handleTIMreply(const std::string replyData);
	bool handleMESreq(unsigned int DBid, unsigned int cmdid, const std::list<std::string> reqData);
	void handleTIMerror();
	void handleTIMtimeout();

	void registerInvoker(unsigned int DBid, XmlBridgeInvoker* invokref) {
		_invokers.insert(std::pair<unsigned int, XmlBridgeInvoker* >(DBid, invokref));
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
	std::map<unsigned int, XmlBridgeInvoker*> _invokers;
	TimIO* _timio;

	/** It is not the exact type since mesbufferer.h is included only in xmlbridgeinvoker.cpp */
	void* _mesbufferer;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
