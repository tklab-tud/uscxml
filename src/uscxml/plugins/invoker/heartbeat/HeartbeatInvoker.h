#ifndef HEARTBEATINVOKER_H_W09J90F0
#define HEARTBEATINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class HeartbeatInvoker : public InvokerImpl {
public:
	HeartbeatInvoker();
	virtual ~HeartbeatInvoker();
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("heartbeat");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#heartbeat");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	static void dispatch(void* instance, std::string name);

protected:
	Event _event;

};

class HeartbeatDispatcher : public DelayedEventQueue {
public:
	static HeartbeatDispatcher* getInstance();
protected:
	static HeartbeatDispatcher* _instance;
	HeartbeatDispatcher();
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(HeartbeatInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: HEARTBEATINVOKER_H_W09J90F0 */
