#ifndef USCXMLINVOKER_H_OQFA21IO
#define USCXMLINVOKER_H_OQFA21IO

#include <uscxml/Interpreter.h>
#include <boost//enable_shared_from_this.hpp>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class Interpreter;

class USCXMLInvoker : public InvokerImpl, public boost::enable_shared_from_this<USCXMLInvoker> {
public:
	USCXMLInvoker();
	virtual ~USCXMLInvoker();
	virtual InvokerImpl* create(Interpreter* interpreter);
	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("uscxml");
		names.insert("http://www.w3.org/TR/scxml");
		names.insert("http://www.w3.org/TR/scxml/");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);
	virtual void sendToParent(const SendRequest& req);

protected:
	std::string _invokeId;
	Interpreter* _invokedInterpreter;
	Interpreter* _parentInterpreter;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(USCXMLInvoker, Invoker);
#endif

}

#endif /* end of include guard: USCXMLINVOKER_H_OQFA21IO */
