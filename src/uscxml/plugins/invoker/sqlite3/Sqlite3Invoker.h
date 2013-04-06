#ifndef SQLITE3INVOKER_H_W09J90F0
#define SQLITE3INVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class Sqlite3Invoker : public InvokerImpl {
public:
	Sqlite3Invoker();
	virtual ~Sqlite3Invoker();
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("sqlite3");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#sqlite3");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(Sqlite3Invoker, InvokerImpl);
#endif

}


#endif /* end of include guard: SQLITE3INVOKER_H_W09J90F0 */
