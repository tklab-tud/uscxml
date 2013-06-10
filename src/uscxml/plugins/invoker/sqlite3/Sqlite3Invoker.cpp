#include "Sqlite3Invoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new Sqlite3InvokerProvider() );
	return true;
}
#endif

Sqlite3Invoker::Sqlite3Invoker() {
}

Sqlite3Invoker::~Sqlite3Invoker() {
};

boost::shared_ptr<InvokerImpl> Sqlite3Invoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<Sqlite3Invoker> invoker = boost::shared_ptr<Sqlite3Invoker>(new Sqlite3Invoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data Sqlite3Invoker::getDataModelVariables() {
	Data data;
	return data;
}

void Sqlite3Invoker::send(const SendRequest& req) {
}

void Sqlite3Invoker::cancel(const std::string sendId) {
}

void Sqlite3Invoker::invoke(const InvokeRequest& req) {
}

}