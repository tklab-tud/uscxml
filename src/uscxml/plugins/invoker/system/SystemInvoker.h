#ifndef SYSTEMINVOKER_H_W09J90F0
#define SYSTEMINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SystemInvoker : public InvokerImpl {
public:
	SystemInvoker();
	virtual ~SystemInvoker();
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("system");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#system");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SystemInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: SYSTEMINVOKER_H_W09J90F0 */
