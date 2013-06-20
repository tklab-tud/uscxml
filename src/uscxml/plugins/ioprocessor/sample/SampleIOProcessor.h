#ifndef SAMPLEIOPROCESSOR_H_2CUY93KU
#define SAMPLEIOPROCESSOR_H_2CUY93KU

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SampleIOProcessor : public IOProcessorImpl {
public:
	SampleIOProcessor();
	virtual ~SampleIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("sample");
		names.insert("http://www.w3.org/TR/scxml/#SampleEventProcessor");
		return names;
	}

	virtual void send(const SendRequest& req);
	Data getDataModelVariables();

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SampleIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: SAMPLEIOPROCESSOR_H_2CUY93KU */