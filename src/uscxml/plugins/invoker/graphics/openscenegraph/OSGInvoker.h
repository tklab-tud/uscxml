#ifndef OSGINVOKER_H_H6T4R8HU
#define OSGINVOKER_H_H6T4R8HU

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OSGInvoker : public Invoker {
public:
	OSGInvoker();
	virtual ~OSGInvoker();
	virtual Invoker* create(Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("3d");
		names.insert("scenegraph");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#3d");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(InvokeRequest& req);
	virtual void sendToParent(SendRequest& req);

protected:
	std::string _invokeId;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OSGInvoker, Invoker);
#endif

}


#endif /* end of include guard: OSGINVOKER_H_H6T4R8HU */
