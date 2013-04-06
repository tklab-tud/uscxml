#ifndef SCXMLIOProcessor_H_2CUY93KU
#define SCXMLIOProcessor_H_2CUY93KU

#include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SCXMLIOProcessor : public BasicHTTPIOProcessor {
public:
	SCXMLIOProcessor();
	virtual ~SCXMLIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("http://www.w3.org/TR/scxml/#SCXMLEventProcessor");
		names.insert("scxml");
		return names;
	}

	virtual void send(const SendRequest& req);

	Data getDataModelVariables();
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SCXMLIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: SCXMLIOProcessor_H_2CUY93KU */