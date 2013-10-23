#include "XmlBridgeInvoker.h"
#include <mesbufferer.h>
#include <regex>

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
	LOG(INFO) << "Creating XmlBridgeInvoker(s) for each datablock";

	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(this);

	invoker->setInterpreter(interpreter);
	invoker->setInvokeId(INVOKER_TYPE + interpreter->getName());
	invoker->setType(INVOKER_TYPE);

	return invoker;
}

void XmlBridgeInvoker::invoke(const InvokeRequest& req) {
	LOG(INFO) << "Invoking XmlBridgeInvoker (source:" <<
		req.getSource() << ", type:" << req.getType() << ")";

	if (req.params.find("timeout") == req.params.end()) {
		LOG(ERROR) << "XmlBridgeInvoker: No timeout param given, assuming 5 seconds";
		_timeoutVal = 5;
	} else
		_timeoutVal = atoi(req.params.find("datablock")->second.atom.c_str());

	_DBid = atoi(_invokeId.c_str() + sizeof(INVOKER_TYPE));

	XmlBridgeInputEvents& myinstance = XmlBridgeInputEvents::getInstance();
	myinstance.registerInvoker(_DBid, this);
}

Data XmlBridgeInvoker::getDataModelVariables() {
	//tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	Data data;
	return data;
}

/** SCXML->TIM | SCXML->MES */
void XmlBridgeInvoker::send(const SendRequest& req) {
	SendRequest reqCopy(req);

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	//_interpreter->getDataModel().replaceExpressions(reqCopy.content);

	if (reqCopy.getName().substr(0, 3) == SCXML2TIM_EV) {
		/* namelist compound data */
		std::map<std::string, Data>::const_iterator nameiter;
		for (nameiter = reqCopy.namelist.begin(); nameiter != reqCopy.namelist.end(); nameiter++)
			bridgeInstance.sendreq2TIM(reqCopy.getName().c_str() + sizeof(SCXML2TIM_EV),
				reqCopy.data.compound[nameiter->first].atom, _timeoutVal);
	} else if (reqCopy.getName().substr(0, 3) == SCXML2MES_EV) {
		/* namelist compound data */
		std::map<std::string, Data>::const_iterator nameiter;
		for (nameiter = reqCopy.namelist.begin(); nameiter != reqCopy.namelist.end(); nameiter++)
			bridgeInstance.sendreply2MES(_DBid, reqCopy.getName().c_str() + sizeof(SCXML2MES_EV),
				reqCopy.data.compound[nameiter->first].atom);
	} else {
		LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request";
		return;
	}
}

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
void XmlBridgeInvoker::buildTIMreply(unsigned int cmdid, const std::string reply_raw_data)
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
		buildTIMexception(cmdid, TIM_ERROR);
		return;
	}

	std::stringstream ss;
	ss << TIM2SCXML_EV << cmdid;

	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		buildTIMexception(cmdid, TIM_ERROR);
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

/** TIM->SCXML */
void XmlBridgeInvoker::buildTIMexception(unsigned int cmdid, exceptions type)
{
	std::stringstream ss;
	switch(type) {
		case TIM_TIMEOUT:
			ss << TIM2SCXML_TIMEOUT << cmdid;
			break;
		default:
			ss << TIM2SCXML_ERROR << cmdid;
			break;
	}

	Event myevent(ss.str(), Event::EXTERNAL);
	myevent.setInvokeId("xmlbridge");
	myevent.setOrigin("TIM");
	myevent.setOriginType("e");
	returnEvent(myevent);
}

/** SCXML -> TIM */
void XmlBridgeInputEvents::sendreq2TIM(const char *cmdid, const std::string reqData, unsigned int timeout)
{
	//check command id and str first
	_timio->_timCmdIds.push(atoi(cmdid));
	_timio->_timCmds.push(reqData);
	_timio->_defTimeout = timeout;
	_timio->_thread = new tthread::thread(TimIO::client, _timio);
}

/** SCXML -> MES */
void XmlBridgeInputEvents::sendreply2MES(unsigned int DBid, const char *cmdid, const std::string replyData)
{
	((MesBufferer *)_mesbufferer)->bufferMESreplyWRITE(DBid, atoi(cmdid), replyData);
}

/**  TIM -> SCXML */
void XmlBridgeInputEvents::handleTIMreply(const std::string replyData)
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMreply(_timio->_timCmdIds.front(), replyData);
		inviter++;
	}
	_timio->_timCmds.pop();
	_timio->_timCmdIds.pop();
}

/**  MES -> SCXML */
bool XmlBridgeInputEvents::handleMESreq(unsigned int DBid, unsigned int cmdid, const std::list <std::string> reqData)
{
	if (_invokers.count(DBid) == 0) {
		LOG(ERROR) << "Datablock not supported by currently active SCXML interpreters and invokers, ignoring MES request";
		return false;
	}
	_invokers[DBid]->buildMESreq(cmdid, reqData);
	return true;
}

XmlBridgeInputEvents::~XmlBridgeInputEvents() {}

void XmlBridgeInputEvents::handleTIMtimeout()
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMexception(_timio->_timCmdIds.front(), TIM_TIMEOUT);
		inviter++;
	}
	_timio->_timCmds.pop();
	_timio->_timCmdIds.pop();
}

void XmlBridgeInputEvents::handleTIMerror()
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMexception(_timio->_timCmdIds.front(), TIM_ERROR);
		inviter++;
	}
	_timio->_timCmds.pop();
	_timio->_timCmdIds.pop();
}

} //namespace uscxml


