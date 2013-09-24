#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <map>
#include <iostream>

#include <uscxml/config.h>
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
	XmlBridgeInvoker();
	virtual ~XmlBridgeInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	void handleReply(const std::string reply_raw_data);
	static void run(void* instance);

protected:

	bool _isRunning;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
};

/* one XmlBridgeSMEvents for each datablock */
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

	static void loadDBFrameID(const uint8_t datablockID, const string dbframeID);
	static void receiveReplyID(const uint8_t datablockID, const char *replyData);

	//std::map<std::string, struct stat> getAllEntries() {}
	static XmlBridgeInputEvents& getInstance() {
		LOG(INFO) << "Initializing XmlBridgeInputEvents instance" << endl;
		static XmlBridgeInputEvents instance;
		return instance;
	}

	XmlBridgeInvoker* _invokPointer;

protected:
	XmlBridgeInputEvents() : _invokPointer(NULL), _initialization(false), _lastChecked(0) {}
	/* second private constructor */
	//XmlBridgeInputEvents(const std::string& dir, const std::string& relDir) : _dir(dir), _relDir(relDir), _recurse(true), _lastChecked(0) {}

	/*std::string _dir;
	std::string _relDir;

	std::map<std::string, struct stat> _knownEntries;
	std::map<std::string, XmlBridgeSMIO*> _knownDirs;
	*/

	bool _initialization;
	time_t _lastChecked;

	//BridgeConfig& _bridgeconf;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
