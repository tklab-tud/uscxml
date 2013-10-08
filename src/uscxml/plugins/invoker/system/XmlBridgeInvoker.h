#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <map>
#include <iostream>

#include <uscxml/Interpreter.h>
#include <glog/logging.h>
//#include "bridgeconfig.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

using namespace std;

namespace uscxml {

class XmlBridgeInvoker : public InvokerImpl {
public:
	XmlBridgeInvoker() : _thread(NULL) {}
	~XmlBridgeInvoker();
	boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	Data getDataModelVariables();
	void send(const SendRequest& req);
	void cancel(const std::string sendId);
	void invoke(const InvokeRequest& req);

	void buildEvent(const std::string reply_raw_data);

	/* move invoker to new thread */
	static void run(void* instance) {
		while(((XmlBridgeInvoker*)instance)->_isRunning) {
			//((XmlBridgeInvoker*)instance)->_watcher->updateEntries();
			tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
		}
	}

protected:
	bool _isRunning;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
};

class XmlBridgeInputEvents {
public:
	/*
	enum Action {
	    ADDED = 1,
	    MODIFIED = 2,
	    DELETED = 4,
	    EXISTING = 8
	}; */

	~XmlBridgeInputEvents() {}

	void handleMESreadreq(const string dbname, const string replyData);
	void handleTIMreply(const string dbname, const string replyData);
	void handleMESwritemsgreq(const string dbname, const string replyData);
	void handleMESwriteboolreq(const string dbname, const string replyData);

	void registerInvoker(std::string smName, XmlBridgeInvoker* invokref) {
		_invokers[smName] = invokref;
	}
	static XmlBridgeInputEvents& getInstance() {
		LOG(INFO) << "Instantiating XmlBridgeInputEvents singleton" << endl;
		static XmlBridgeInputEvents instance;
		return instance;
	}

private:
	XmlBridgeInputEvents() : _lastChecked(0) {}
	XmlBridgeInputEvents& operator=( const XmlBridgeInputEvents& );

	std::map<std::string, XmlBridgeInvoker*> _invokers;
	time_t _lastChecked;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
