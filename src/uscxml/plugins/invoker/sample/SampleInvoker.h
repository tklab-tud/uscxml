#ifndef SAMPLEINVOKER_H_W09J90F0
#define SAMPLEINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SampleInvoker : public InvokerImpl {
public:
	SampleInvoker();
	virtual ~SampleInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("sample");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#sample");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SampleInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: SAMPLEINVOKER_H_W09J90F0 */
