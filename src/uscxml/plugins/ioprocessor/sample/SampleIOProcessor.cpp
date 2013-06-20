#include <uscxml/Common.h>
#include "uscxml/plugins/ioprocessor/sample/SampleIOProcessor.h"
#include "uscxml/Message.h"
#include <iostream>

#include <string.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new SampleIOProcessorProvider() );
	return true;
}
#endif

SampleIOProcessor::SampleIOProcessor() {
}

SampleIOProcessor::~SampleIOProcessor() {
}

boost::shared_ptr<IOProcessorImpl> SampleIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SampleIOProcessor> io = boost::shared_ptr<SampleIOProcessor>(new SampleIOProcessor());
	return io;
}

Data SampleIOProcessor::getDataModelVariables() {
	Data data;
	return data;
}

void SampleIOProcessor::send(const SendRequest& req) {
}

}