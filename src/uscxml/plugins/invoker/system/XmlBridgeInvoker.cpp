#include "XmlBridgeInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add(new XmlBridgeInvokerProvider());
	return true;
}
#endif

XmlBridgeInvoker::XmlBridgeInvoker() :
	_thread(NULL),
	_watcher(NULL) {
}

XmlBridgeInvoker::~XmlBridgeInvoker() {
	_isRunning = false;
	if (_thread) {
		_thread->join();
		delete _thread;
	}
	if (_watcher)
		delete(_watcher);
};

XmlBridgeInvoker::XmlBridgeInvoker() {
}

XmlBridgeInvoker::~XmlBridgeInvoker() {
};

boost::shared_ptr<InvokerImpl> XmlBridgeInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(new XmlBridgeInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data XmlBridgeInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void XmlBridgeInvoker::send(const SendRequest& req) {
	//TODOOOOOO!!
}

void XmlBridgeInvoker::cancel(const std::string sendId) {
}

void XmlBridgeInvoker::invoke(const InvokeRequest& req) {
	if (req.params.find("datablock") == req.params.end()) {
		LOG(ERROR) << "No datablock param given";
		return;
	}

	/*
	if (boost::iequals(req.params.find("reportexisting")->second, "false"))
		_reportExisting = false;
	if (req.params.find("recurse") != req.params.end() &&
		boost::iequals(req.params.find("recurse")->second, "true"))
		_recurse = true;
	if (req.params.find("reporthidden") != req.params.end() &&
		boost::iequals(req.params.find("reporthidden")->second, "true"))
		_reportHidden = true;

	std::string suffixList;
	if (req.params.find("suffix") != req.params.end()) {
		suffixList = req.params.find("suffix")->second;
	} else if (req.params.find("suffixes") != req.params.end()) {
		suffixList = req.params.find("suffixes")->second;
	}*/



	if (_bridgeconf.getDBFrameList())

	if (suffixList.size() > 0) {
		// seperate path into components
		std::stringstream ss(suffixList);
		std::string item;
		while(std::getline(ss, item, ' ')) {
			if (item.length() == 0)
				continue;
			_suffixes.insert(item);
		}
	}

	std::multimap<std::string, std::string>::const_iterator dirIter = req.params.find("dir");
	while(dirIter != req.params.upper_bound("dir")) {
		URL url(dirIter->second);
		if (!url.toAbsolute(_interpreter->getBaseURI()) || !boost::iequals(url.scheme(), "file")) {
			LOG(ERROR) << "Given directory '" << dirIter->second << "' cannot be transformed to absolute path";
		} else {
			_dir = url.path();
		}
		break;
	}


	if _watcher = new XmlBridgeSMIO(_dir, _recurse);
	_watcher->addMonitor(this);
	_watcher->updateEntries(true);

	_isRunning = true;
	_thread = new tthread::thread(XmlBridgeInvoker::run, this);
}

void XmlBridgeInvoker::run(void* instance) {
	while(((XmlBridgeInvoker*)instance)->_isRunning) {
		//((XmlBridgeInvoker*)instance)->_watcher->updateEntries();
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
	}
}

}
