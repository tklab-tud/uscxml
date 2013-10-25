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
	LOG(INFO) << "Creating XmlBridgeInvoker(s) for each datablock";

	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(this);

	invoker->setInterpreter(interpreter);
	invoker->setInvokeId(INVOKER_TYPE + interpreter->getName());
	invoker->setType(INVOKER_TYPE);

	return invoker;
}

void XmlBridgeInvoker::invoke(const InvokeRequest& req) {
	LOG(INFO) << "Invoking XmlBridgeInvoker " << _invokeId;

	if (req.params.find("timeout") == req.params.end()) {
		LOG(ERROR) << "XmlBridgeInvoker: No timeout param given, assuming 5 seconds";
		_timeoutVal = 5;
	} else
		_timeoutVal = atoi(req.params.find("timeout")->second.atom.c_str());

	_DBid = atoi(_invokeId.substr(sizeof(INVOKER_TYPE)).c_str());

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
	SendRequest reqCopy = req;
	std::string evName = reqCopy.getName();
	int index = evName.find('_');
	bool write = (evName.c_str()[index + 1] == 'w');
	std::string evType = evName.substr(index + 2, 3);
	unsigned int cmdid = atoi(evName.substr(0, index - 1).c_str());

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	//_interpreter->getDataModel().replaceExpressions(reqCopy.content);

	std::map<std::string, Data>::const_iterator nameiter;
	for (nameiter = reqCopy.namelist.begin(); nameiter != reqCopy.namelist.end(); nameiter++) {
		if (evType == SCXML2TIM) {
			bridgeInstance.sendReq2TIM(cmdid, write, reqCopy.data.compound[nameiter->first].atom, _timeoutVal);
		} else if (evType == SCXML2MES_ACK) {
			bridgeInstance.sendReply2MES(_DBid, cmdid, write,
				write ? std::string() : reqCopy.data.compound[nameiter->first].atom);
		} else if (evType == SCXML2MES_ERR) {
			bridgeInstance.sendErr2MES(_DBid, cmdid, write);
			return;
		} else {
			LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request\n"
				<< "The event name in the SCXML file is propably incorrect.";
			return;
		}
	}
}

/** MES->SCXML */
void XmlBridgeInvoker::buildMESreq(unsigned int cmdid, bool write, const std::list < std::string > req_raw_data) {
	std::stringstream ss;
	ss << cmdid << '_' << (write ? WRITEOP : READOP) << MES2SCXML;

	Event myevent(ss.str(), Event::EXTERNAL);

	if (write && !req_raw_data.empty()) {
		Data mydata;

		std::list<std::string>::const_iterator myiter;
		for(myiter = req_raw_data.begin(); myiter != req_raw_data.end(); myiter++)
			mydata.array.push_back(Data(*myiter));

		myevent.data = mydata;
	}

	returnEvent(myevent);
}

/** TIM->SCXML */
void XmlBridgeInvoker::buildTIMreply(unsigned int cmdid, bool type, const std::string reply_raw_data)
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
	ss << cmdid << '_' << (type ? WRITEOP : READOP) << TIM2SCXML;

	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		buildTIMexception(cmdid, TIM_ERROR);
		return;
	}
	myevent.dom = domParser.getDocument().getDocumentElement();

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
	returnEvent(myevent);
}

/** SCXML -> TIM */
void XmlBridgeInputEvents::sendReq2TIM(unsigned int cmdid, bool write, const std::string reqData, unsigned int timeout)
{
	//check command id and str first
	_timio->_timCmdId.push(cmdid);
	_timio->_timCmd.push(reqData);
	_timio->_timCmdWrite.push(write);
	_timio->_defTimeout = timeout;
	_timio->_thread = new tthread::thread(TimIO::client, _timio);
	_timio->_thread->detach();
}

/** SCXML -> MES */
void XmlBridgeInputEvents::sendReply2MES(unsigned int DBid, unsigned int cmdid, bool write, const std::string replyData)
{
	if (write)
		((MesBufferer *)_mesbufferer)->bufferMESreplyWRITE(DBid, cmdid);
	else
		((MesBufferer *)_mesbufferer)->bufferMESreplyREAD(DBid, cmdid, replyData);
}


/** SCXML -> MES */
void XmlBridgeInputEvents::sendErr2MES(unsigned int DBid, unsigned int cmdid, bool write)
{
	((MesBufferer *)_mesbufferer)->bufferMESerror(DBid, cmdid, write);
}

/**  TIM -> SCXML */
void XmlBridgeInputEvents::handleTIMreply(const std::string replyData)
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMreply(_timio->_timCmdId.front(), _timio->_timCmdWrite.front(), replyData);
		inviter++;
	}
	_timio->_timCmd.pop();
	_timio->_timCmdId.pop();
	_timio->_timCmdWrite.pop();
}

/**  MES -> SCXML */
bool XmlBridgeInputEvents::handleMESreq(unsigned int DBid, unsigned int cmdid,
				 bool write, const std::list <std::string> reqData)
{
	if (_invokers.count(DBid) == 0) {
		LOG(ERROR) << "Datablock not supported by currently active SCXML interpreters and invokers, ignoring MES request";
		return false;
	}
	_invokers[DBid]->buildMESreq(cmdid, write, reqData);
	return true;
}

/**  TIM -> SCXML */
void XmlBridgeInputEvents::handleTIMexception(exceptions type)
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMexception(_timio->_timCmdId.front(), type);
		inviter++;
	}
	_timio->_timCmd.pop();
	_timio->_timCmdId.pop();
	_timio->_timCmdWrite.pop();
}

} //namespace uscxml