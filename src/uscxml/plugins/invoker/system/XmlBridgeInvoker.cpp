#include "XmlBridgeInvoker.h"

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
	_thread(NULL)
{
		XmlBridgeInputEvents& myinstance = XmlBridgeInputEvents::getInstance();
		myinstance._invokPointer = this;
		LOG(INFO) << "Initializing XmlBridgeInvoker instance" << endl;
}

XmlBridgeInvoker::~XmlBridgeInvoker() {
	_isRunning = false;
	if (_thread) {
		_thread->join();
		delete _thread;
	}
}

boost::shared_ptr<InvokerImpl> XmlBridgeInvoker::create(InterpreterImpl* interpreter) {
	LOG(INFO) << "Creating XmlBridgeInvoker instance" << endl;

	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(new XmlBridgeInvoker());

	invoker->setInterpreter(interpreter);
	invoker->setInvokeId("xmlbridge1");
	invoker->setType("xmlbridge");

	return invoker;
}

Data XmlBridgeInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void XmlBridgeInvoker::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	SendRequest reqCopy(req);

	//leggere parametri

	//estrarre la struttura XML del messaggio da inviare al TIM

	//riempire i campi del messaggio XML al tim con i field ricevuti dal Modbus

	_interpreter->getDataModel().replaceExpressions(reqCopy.content);

	std::cout << std::endl << reqCopy.getXML() << std::endl;
	std::cout << std::endl << reqCopy.getContent() << std::endl;
	std::cout << std::endl << reqCopy.getData() << std::endl;
	std::cout << std::endl << reqCopy.getRaw() << std::endl;

	//Data xml = Data::fromXML(reqCopy.content);
	//if (xml) {
	//	reqCopy.data = xml;
	//	cout << xml.toXMLString() << endl;
	//} else
	//	cerr << "Failed parsing send request" << endl;*/

	//cout << reqCopy.toXMLString() << endl;

	/* lock automatically released */

	/*
	if(!_longPoll) {
		_outQueue.push_back(reqCopy);
		return;
	}
	reply(reqCopy, _longPoll);
	_longPoll.curlReq = NULL;

	//2
	std::stringstream domSS;*/

	/*
	if (req.dom) {
		// hack until jVoiceXML supports XML
		std::cout << req.dom;
		Arabica::DOM::NodeList<std::string> prompts = req.dom.getElementsByTagName("vxml:prompt");
		for (int i = 0; i < prompts.getLength(); i++) {
			if (prompts.item(i).hasChildNodes()) {
				domSS << prompts.item(i).getFirstChild().getNodeValue() << ".";
			}
		}
	}
	*/

	/*
	domSS << req.getFirstDOMElement();
	domSS << req.dom;
	*/

	//_interpreter->getDataModel().replaceExpressions(start.content);
}

void XmlBridgeInvoker::cancel(const std::string sendId) {
}

void XmlBridgeInvoker::invoke(const InvokeRequest& req) {

	LOG(INFO) << "Invoking XmlBridge" << endl;

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
	}
	*/


	/*
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
	*/

	/*
	_watcher = new XmlBridgeSMIO(_dir, _recurse);
	_watcher->addMonitor(this);
	_watcher->updateEntries(true);
	*/

	_isRunning = true;
	LOG(INFO) << "Moving XmlBridgeInvoker to a new thread" << endl;
	_thread = new tthread::thread(XmlBridgeInvoker::run, this);
}

void XmlBridgeInvoker::handleReply(const std::string reply_raw_data) {

	//  std::cout << action << " on " << reportedFilename << std::endl;

	/*
	std::string path;         // complete path to the file including filename
	std::string relPath;      // path relative to monitored directory including filename
	std::string dir;          // the name of the directory we monitor
	std::string relDir;       // the directory from dir to the actual directory where we found a file
	std::string basename;     // filename including suffix
	std::string strippedName; // filename without the suffix
	std::string extension;    // the extension
	*/

	/*
	dir = reportedDir;

	path = dir + reportedFilename;
	boost::algorithm::replace_all(path, "\\", "/");
	boost::algorithm::replace_all(path, "//", "/");

	assert(boost::algorithm::starts_with(path, dir));
	relPath = path.substr(dir.length());
	assert(boost::equal(path, dir + relPath));

	size_t lastSep;
	if ((lastSep = path.find_last_of(PATH_SEPERATOR)) != std::string::npos) {
		lastSep++;
		basename = path.substr(lastSep, path.length() - lastSep);
	} else {
		assert(false);
	}
	assert(boost::algorithm::ends_with(relPath, basename));

	// extension is the suffix and strippedName the basename without the suffix
	size_t lastDot;
	if ((lastDot = basename.find_last_of(".")) != std::string::npos) {
		if (lastDot == 0) {
			// hidden file
			strippedName = basename;
		} else {
			extension = basename.substr(lastDot + 1);
			strippedName = basename.substr(0, lastDot);
		}
	} else {
		strippedName = basename;
	}

	relDir = relPath.substr(0, relPath.length() - basename.length());
	assert(boost::equal(path, dir + relDir + basename));

	// return if this is a hidden file
	if (boost::algorithm::starts_with(basename, ".") && !_reportHidden)
		return;

	// ilter suffixes
	if (_suffixes.size() > 0) {
		bool validSuffix = false;
		std::set<std::string>::iterator suffixIter = _suffixes.begin();
		while(suffixIter != _suffixes.end()) {
			if (boost::algorithm::ends_with(path, *suffixIter)) {
				validSuffix = true;
				break;
			}
			suffixIter++;
		}
		if (!validSuffix)
			return;
	}
	*/

	LOG(INFO) << "Building Event" << endl;
	uscxml::Event myevent("reply", uscxml::Event::EXTERNAL);
	//event.setName("reply." + _interpreter->getState())

	LOG(INFO) << "Building Event Data from RawData" << endl;
	const uscxml::Data eventdata(reply_raw_data);

	LOG(INFO) << "Setting Event Data" << endl;
	myevent.setData(eventdata);

	/*
	if (action != DirectoryWatch::DELETED) {
		event.data.compound["file"].compound["mtime"] = toStr(fileStat.st_mtime);
		event.data.compound["file"].compound["ctime"] = toStr(fileStat.st_ctime);
		event.data.compound["file"].compound["atime"] = toStr(fileStat.st_atime);
		event.data.compound["file"].compound["size"]  = toStr(fileStat.st_size);
	}

	event.data.compound["file"].compound["name"] = Data(basename, Data::VERBATIM);
	event.data.compound["file"].compound["extension"] = Data(extension, Data::VERBATIM);
	event.data.compound["file"].compound["strippedName"] = Data(strippedName, Data::VERBATIM);
	event.data.compound["file"].compound["relPath"] = Data(relPath, Data::VERBATIM);
	event.data.compound["file"].compound["relDir"] = Data(relDir, Data::VERBATIM);
	event.data.compound["file"].compound["path"] = Data(path, Data::VERBATIM);
	event.data.compound["file"].compound["dir"] = Data(dir, Data::VERBATIM);
	*/

	LOG(INFO) << "Sending Event to StateMachine" << endl;
	returnEvent(myevent);
}

void XmlBridgeInputEvents::receiveReply(const uint8_t datablockID, const char *replyData)
{
	string repdata(replyData);
	XmlBridgeInputEvents myinstance = XmlBridgeInputEvents::getInstance();
	myinstance._invokPointer->handleReply(repdata);
}


}
/*
XmlBridgeInputEvents::~XmlBridgeInputEvents() {
	std::map<std::string, DirectoryWatch*>::iterator dirIter = _knownDirs.begin();
	while(dirIter != _knownDirs.end()) {
		delete(dirIter->second);
		dirIter++;
	}
}
*/
