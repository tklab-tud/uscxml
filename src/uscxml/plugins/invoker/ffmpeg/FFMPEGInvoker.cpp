#include "FFMPEGInvoker.h"
#include <glog/logging.h>

#include <libavcodec/avcodec.h>
#include <libavformat/avformat.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new FFMPEGInvokerProvider() );
	return true;
}
#endif

FFMPEGInvoker::FFMPEGInvoker() {
}

FFMPEGInvoker::~FFMPEGInvoker() {
};

boost::shared_ptr<IOProcessorImpl> FFMPEGInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<FFMPEGInvoker> invoker = boost::shared_ptr<FFMPEGInvoker>(new FFMPEGInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data FFMPEGInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void FFMPEGInvoker::send(const SendRequest& req) {
}

void FFMPEGInvoker::cancel(const std::string sendId) {
}

void FFMPEGInvoker::invoke(const InvokeRequest& req) {
//  AVIOContext* avCtx = avio_alloc_context();
}

}