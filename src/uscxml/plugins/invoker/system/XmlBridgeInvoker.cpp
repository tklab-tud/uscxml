#include "XmlBridgeInvoker.h"
#include <mesbufferer.h>

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

boost::shared_ptr<InvokerImpl> XmlBridgeInvoker::create(InterpreterImpl* interpreter) {
	LOG(INFO) << "Creating XmlBridgeInvoker invoker";

	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(this);

	invoker->setInterpreter(interpreter);
	invoker->setInvokeId("xmlbridge1");
	invoker->setType("xmlbridge");

	return invoker;
}

void XmlBridgeInvoker::invoke(const InvokeRequest& req) {
	LOG(INFO) << "Invoking XmlBridgeInvoker";

	if (req.params.find("datablock") == req.params.end()) {
		LOG(ERROR) << "No datablock param given";
		return;
	}

	_DBid = req.params.find("datablock")->second.atom;

	XmlBridgeInputEvents& myinstance = XmlBridgeInputEvents::getInstance();
	myinstance.registerInvoker(_DBid, this);
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
	_watcher = new XmlBridgeSMIO(_dir, _recurse);
	_watcher->addMonitor(this);
	_watcher->updateEntries(true);
	*/

Data XmlBridgeInvoker::getDataModelVariables() {
	//tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	Data data;
	return data;
}
	/*data.compound["dir"] = Data(_dir, Data::VERBATIM);

//	std::set<std::string>::iterator suffixIter = _suffixes.begin();
//	while(suffixIter != _suffixes.end()) {
//		data.compound["suffixes"].array.push_back(Data(*suffixIter, Data::VERBATIM));
//		suffixIter++;
//	}

//	std::map<std::string, struct stat> entries = _watcher->getAllEntries();
//	std::map<std::string, struct stat>::iterator entryIter = entries.begin();
//	while(entryIter != entries.end()) {
//		data.compound["file"].compound[entryIter->first].compound["mtime"] = toStr(entryIter->second.st_mtime);
//		data.compound["file"].compound[entryIter->first].compound["ctime"] = toStr(entryIter->second.st_mtime);
//		data.compound["file"].compound[entryIter->first].compound["atime"] = toStr(entryIter->second.st_mtime);
//		data.compound["file"].compound[entryIter->first].compound["size"] = toStr(entryIter->second.st_mtime);
//		entryIter++;
//	} */

/** SCXML->TIM | SCXML->MES */
void XmlBridgeInvoker::send(const SendRequest& req) {
	SendRequest reqCopy(req);

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	//_interpreter->getDataModel().replaceExpressions(reqCopy.content);

	if (reqCopy.getName().substr(0, 3) == SCXML2TIM_EV) {
		/* namelist compound data */
		std::map<std::string, Data>::const_iterator nameiter;
		for (nameiter = reqCopy.namelist.begin(); nameiter != reqCopy.namelist.end(); nameiter++)
			bridgeInstance.sendreq2TIM(reqCopy.getName().c_str()[sizeof(SCXML2TIM_EV)-1],
				reqCopy.data.compound[nameiter->first].atom);
	} else if (reqCopy.getName().substr(0, 3) == SCXML2MES_EV) {
		/* namelist compound data */
		std::map<std::string, Data>::const_iterator nameiter;
		for (nameiter = reqCopy.namelist.begin(); nameiter != reqCopy.namelist.end(); nameiter++)
			bridgeInstance.sendreply2MES(_DBid, reqCopy.getName().c_str()[sizeof(SCXML2MES_EV)-1],
				reqCopy.data.compound[nameiter->first].atom);
	} else {
		LOG(ERROR) << "Unsupported event type";
		return;
	}
}

/*
	build xml output

	lock automatically released


	if(!_longPoll) {
		_outQueue.push_back(reqCopy);
		return;
	}
	reply(reqCopy, _longPoll);
	_longPoll.curlReq = NULL;

	//2
	std::stringstream domSS;

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

	domSS << req.dom;

	//_interpreter->getDataModel().replaceExpressions(start.content);
*/

/** MES->SCXML */
void XmlBridgeInvoker::buildMESreq(unsigned int cmdid, const std::list < std::string > req_raw_data) {
	std::stringstream ss;
	ss << MES2SCXML_EV << cmdid;

	Event myevent(ss.str(), Event::EXTERNAL);
	myevent.setInvokeId("xmlbridge");
	myevent.setOrigin("MES");

	if (req_raw_data.empty()) {
		myevent.setOriginType("r");
	} else {
		myevent.setOriginType("w");

		Data mydata;

		std::list<std::string>::const_iterator myiter;
		for(myiter = req_raw_data.begin(); myiter != req_raw_data.end(); myiter++)
			mydata.array.push_back(Data(*myiter));

		myevent.data = mydata;
	}

	returnEvent(myevent);
}

/** TIM->SCXML */
void XmlBridgeInvoker::buildTIMreply(const char cmdid, const std::string reply_raw_data)
{
	Arabica::SAX2DOM::Parser<std::string> domParser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	domParser.setErrorHandler(errorHandler);

	std::istringstream is(reply_raw_data);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(is);

	if (!(domParser.parse(inputSource))) {
		LOG(ERROR) << "Failed parsing TIM XML reply string for command " << cmdid;
		LOG(ERROR) << "Errors " << errorHandler.errors();;
		LOG(ERROR) << "TIM XML string was: " << std::endl << reply_raw_data;
		return;
	}

	std::stringstream ss;
	ss << TIM2SCXML_EV << cmdid;

	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		return;
	}
	myevent.dom = domParser.getDocument().getDocumentElement();

	myevent.setInvokeId("xmlbridge");
	myevent.setOrigin("TIM");
	if (reply_raw_data.empty())
		myevent.setOriginType("r");
	else
		myevent.setOriginType("w");

	returnEvent(myevent);
}

	/*  std::cout << action << " on " << reportedFilename << std::endl;

	std::string path;         // complete path to the file including filename
	std::string relPath;      // path relative to monitored directory including filename
	std::string dir;          // the name of the directory we monitor
	std::string relDir;       // the directory from dir to the actual directory where we found a file
	std::string basename;     // filename including suffix
	std::string strippedName; // filename without the suffix
	std::string extension;    // the extension

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

/** SCXML -> TIM */
void XmlBridgeInputEvents::sendreq2TIM(const char cmdid, const std::string reqData)
{
	//mutex?

	if (!_timio->_timCmds.empty())
		_timio->_timCmds.pop();
	if (!_timio->_timCmdIds.empty())
		_timio->_timCmdIds.pop();

	//check command id and str first
	_timio->_timCmdIds.push(cmdid);
	_timio->_timCmds.push(reqData);
	_timio->_thread = new tthread::thread(TimIO::client, _timio);
	_timio->_thread->detach();
}

/** SCXML -> MES */
void XmlBridgeInputEvents::sendreply2MES(std::string DBid, const char cmdid, const std::string replyData)
{
	((MesBufferer *)_mesbufferer)->bufferMESreplyWRITE(atoi(DBid.c_str()), atoi(&cmdid), replyData);
}

/**  TIM -> SCXML */
void XmlBridgeInputEvents::handleTIMreply(const char cmdid, const std::string replyData)
{
	std::map<std::string, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMreply(cmdid, replyData);
		inviter++;
	}
}

/**  MES -> SCXML */
void XmlBridgeInputEvents::handleMESreq(unsigned int DBid, unsigned int cmdid, const std::list <std::string> reqData)
{
	std::stringstream ss;
	ss << std::dec << DBid;
	if (_invokers.count(ss.str()) == 0) {
		LOG(ERROR) << "Datablock not supported, ignoring request";
		return;
	}
	_invokers[ss.str()]->buildMESreq(cmdid, reqData);
}

XmlBridgeInputEvents::~XmlBridgeInputEvents() {}

} //namespace uscxml


