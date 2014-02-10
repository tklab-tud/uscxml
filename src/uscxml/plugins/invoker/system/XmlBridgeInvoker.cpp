/*
 * Use is subject to license terms.
 * Copyright (c) 2013, Ajile di Antonio Iudici. All rights reserved.
 *	<antonio.iudici@ajile.it>
 *	<enrico.papi@ajile.it>
 */

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

/**
 * @brief Crea e Registra un Invoker all'interprete SCXML.
 *	Metodo eseguito per ogni elemento <invoke> nell'SCXML
 *
 * @param interpreter	L'interprete chiamante
 * @return boost::shared_ptr<InvokerImpl>	Il puntatore all'invoker.
 */
boost::shared_ptr<InvokerImpl> XmlBridgeInvoker::create(InterpreterImpl* interpreter) {
	LOG(INFO) << "Creating XmlBridgeInvoker(s) for each datablock";

	boost::shared_ptr<XmlBridgeInvoker> invoker = boost::shared_ptr<XmlBridgeInvoker>(this);

	/* Scorro l'elenco dei datablock gestiti specificati nel nome dell'SCXML
	 * Per il primo DBid del quale non esiste un invoker registro un nuovo invoker. */
	std::size_t current;
	std::size_t next = -1;
	do {
		current = next + 1;
		next = interpreter->getName().find_first_of(DBID_DELIMITER, current);
		if (interpreter->getInvokers().count(INVOKER_TYPE + interpreter->getName().substr(current, next - current)) == 0) {
			invoker->setInvokeId(INVOKER_TYPE + interpreter->getName());
			break;
		}
	} while (next != std::string::npos);

	invoker->setType(INVOKER_TYPE);
	invoker->setInterpreter(interpreter);
	return invoker;
}

/**
 * @brief Finalizza l'invocazione di un Invoker. Configura l'invoker secondo i parametri inseriti nell'SCXML.
 * @param req Richiesta di Invoke
 */
void XmlBridgeInvoker::invoke(const InvokeRequest& req) {
	LOG(INFO) << "Invoking XmlBridgeInvoker " << _invokeId;

	if (req.params.find("timeout") == req.params.end()) {
		LOG(ERROR) << "XmlBridgeInvoker: No timeout param given, assuming 5 seconds";
		_timeoutVal = 5;
	} else
		_timeoutVal = atoi(req.params.find("timeout")->second.atom.c_str());

	_CMDid = atoi(_invokeId.substr(sizeof(INVOKER_TYPE)).c_str());

	XmlBridgeInputEvents& myinstance = XmlBridgeInputEvents::getInstance();
	myinstance.registerInvoker(_DBid, this);
}

/**
 * @brief Non utilizzata
 * @return Data
 */
Data XmlBridgeInvoker::getDataModelVariables() {
	//tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	Data data;
	return data;
}

/** SCXML->TIM | SCXML->MES */
/**
 * @brief Invia dati generati dall'interprete SCXML (valori XPATH) al MES o al TIM
 *	secondo il tipo di richiesta tramite il singleton XmlBridgeInputEvents
 * @param req La richiesta specificata nell'elemento <send> dell'SCXML
 */
void XmlBridgeInvoker::send(const SendRequest& req) {
	//TODO HANDLE MALFORMED EVENT NAME and DATA

	SendRequest reqCopy = req;
	std::string evName = reqCopy.getName();
	bool write = (evName.c_str()[0] == WRITEOP);
	std::string evType = evName.substr(1, 3);

	XmlBridgeInputEvents& bridgeInstance = XmlBridgeInputEvents::getInstance();
	//_interpreter->getDataModel().replaceExpressions(reqCopy.content);
	//TODO LOG EVENT

	/* I dati inviati dal SCXML all'TIM o al MES sono sempre mappati nella struttura dati 'namelist' dell'evento */
	/* SCXML -> TIM */
	if (evType == SCXML2TIM) {
		//TODO HANDLE MALFORMED SCXML and DATA

		std::stringstream ss;
		std::map<std::string, Data>::const_iterator namelistIter = reqCopy.namelist.begin();
		while(namelistIter != reqCopy.namelist.end()) {
			std::map<std::string, Data>::const_iterator nodesIter = namelistIter->second.compound.begin();
			while(nodesIter != namelistIter->second.compound.end()) {
				ss << nodesIter->second.node;
				nodesIter++;
			}
			namelistIter++;
		}

		/* Elimina SCXML namespace */
		int index = ss.str().find('>');
		if (index == std::string::npos) {
			LOG(ERROR) << "Invalid TIM frame";
			buildTIMexception(_CMDid, TIM_ERROR);
		}
		std::string timstr = "<frame>" + ss.str().substr(index + 1, ss.str().length());

		bridgeInstance.sendReq2TIM(_CMDid, write, timstr, _timeoutVal);

	/* SCXML -> MES */
	} else if (evType == SCXML2MES_ACK) {
		//TODO HANDLE MALFORMED SCXML and DATA

		if (!write) {
			std::map<std::string, Data>::const_iterator namelistIter = reqCopy.namelist.begin();
			while(namelistIter != reqCopy.namelist.end()) {
				std::map<std::string, Data>::const_iterator nodesIter = namelistIter->second.compound.begin();
				while(nodesIter != namelistIter->second.compound.end()) {
					_itemsRead.push_back(nodesIter->second.node.getNodeValue());
					nodesIter++;
				}
				namelistIter++;
			}
		}

		if (_itemsRead.size() >= _currItems || write)
			bridgeInstance.sendReply2MES(_CMDid, _currAddr, _currLen, write, _itemsRead);

	/* SCXML -> MES (errore) */
	} else if (evType == SCXML2MES_ERR) {
		bridgeInstance.sendErr2MES(_CMDid);
	} else {
		LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request\n"
			<< "Propably the event name in the SCXML file is incorrect.";
	}
}

/** MES->SCXML */
/**
 * @brief Genera un evento per l'interprete SCXML corrispondente ad una richiesta MES
 *
 * @param cmdid Il TIM cmd ID
 * @param write	Indica se si tratta di una richiesta di scrittura
 * @param req_raw_data La lista delle stringhe utilizzate per popolare il comando TIM (se richiesta di scrittura)
 */
void XmlBridgeInvoker::buildMESreq(unsigned int addr, unsigned int len, bool write, const std::list<std::string> req_raw_data) {
	std::stringstream ss;
	ss << _CMDid << '_' << (write ? WRITEOP : READOP) << MES2SCXML;

	Event myevent(ss.str(), Event::EXTERNAL);

	/* I dati inviati dal MES all'SCXML sono sempre mappati nella struttura dati 'array' dell'evento */
	if (!req_raw_data.empty()) {
		Data mydata;

		std::list<std::string>::const_iterator myiter;
		for(myiter = req_raw_data.begin(); myiter != req_raw_data.end(); myiter++)
			mydata.array.push_back(Data(*myiter));

		myevent.data = mydata;
		_currItems = req_raw_data.size();
	} else {
		_currItems = 0;
	}
	_currAddr = addr;
	_currLen = len;
	_itemsRead.clear();

	returnEvent(myevent);
}

/** TIM->SCXML */
/**
 * @brief Effettua il parsing di un frammento XML inviato dal TIM verso il gateway.
 *	Genera un evento SCXML con la struttura dati risultante
 *
 * @param cmdid Il TIM cmd ID
 * @param type Lettura/Scrittura
 * @param reply_raw_data Stringa Raw della risposta dal TIM
 */
void XmlBridgeInvoker::buildTIMreply(bool type, const std::string reply_raw_data)
{
	Arabica::SAX2DOM::Parser<std::string> domParser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	domParser.setErrorHandler(errorHandler);

	std::istringstream is(reply_raw_data);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(is);

	if (!(domParser.parse(inputSource))) {
		LOG(ERROR) << "Failed parsing TIM XML reply string for command " << _CMDid;
		LOG(ERROR) << "Errors " << errorHandler.errors();;
		buildTIMexception(_CMDid, TIM_ERROR);
		return;
	}

	std::stringstream ss;
	ss << _CMDid << '_' << (type ? WRITEOP : READOP) << TIM2SCXML;

	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		buildTIMexception(_CMDid, TIM_ERROR);
		return;
	}

	/* I dati inviati dal SCXML all'SCXML sono sempre mappati nella struttura dati 'dom' dell'evento */
	myevent.dom = domParser.getDocument().getDocumentElement();

	returnEvent(myevent);
}

/** TIM->SCXML */
/**
 * @brief Segnala all'SCXML che il thread del client TIM ha generato un'eccezione.
 *
 * @param cmdid Il TIM cmd ID
 * @param type Tipo di eccezione
 */
void XmlBridgeInvoker::buildTIMexception(exceptions type)
{
	std::stringstream ss;
	switch(type) {
		case TIM_TIMEOUT:
			ss << TIM2SCXML_TIMEOUT << _CMDid;
			break;
		default:
			ss << TIM2SCXML_ERROR << _CMDid;
			break;
	}

	Event myevent(ss.str(), Event::EXTERNAL);
	returnEvent(myevent);
}

/** SCXML -> TIM */
/**
 * @brief Configura il thread del client TIM ad inviare un nuovo comando
 *
 * @param cmdid Il TIM cmd ID
 * @param write Lettura/Scrittura
 * @param reqData Dati del comando
 * @param timeout Timeout da impostare
 */
void XmlBridgeInputEvents::sendReq2TIM(unsigned int cmdid, bool write, const std::string reqData, unsigned int timeout)
{
	if (reqData.empty() || timeout == 0) {
		handleTIMexception(TIM_ERROR);
		return;
	}

	_timio->_timCmdId.push(cmdid);
	_timio->_timCmd.push(reqData);
	_timio->_timCmdWrite.push(write);

	_timio->_defTimeout = timeout;
	_timio->_thread = new tthread::thread(TimIO::client, _timio);
	_timio->_thread->detach();
}

/** SCXML -> MES */
/**
 * @brief Invia al MES i dati generati dall'SCXML (valori XPATH) da una risposta del TIM
 *
 * @param DBid Il Datablock ID
 * @param cmdid Il TIM cmd ID
 * @param write Lettura/Scrittura
 * @param replyData Dati della risposta
 */
void XmlBridgeInputEvents::sendReply2MES(unsigned int cmdid, unsigned int addr, unsigned int len,
					 bool write, const std::list<std::string> replyData)
{
	/* L'istanza dell'invoker, corrispondente al comando corrente, mette in coda i dati della risposta del TIM
	 * Quando MesBufferer avrà terminato di bufferizzare la risposta precedente, il comando SCXML <send> ritorna */
	if (write)
		((MesBufferer *)_mesbufferer)->bufferMESreplyWRITE(cmdid);
	else
		((MesBufferer *)_mesbufferer)->bufferMESreplyREAD(cmdid, addr, len, replyData);
}


/** SCXML -> MES */
/**
 * @brief Segnala al Modbus Slave che l'ultima operazione ha generato un'eccezione
 *
 * @param DBid Il Datablock ID
 * @param cmdid Il TIM cmd ID
 */
void XmlBridgeInputEvents::sendErr2MES(unsigned int cmdid)
{
	((MesBufferer *)_mesbufferer)->bufferMESerror(DBid, cmdid);
}

/**  TIM -> SCXML */
/**
 * @brief Riceve i dati inviati dal TIM e costruisce una risposta analizzabile dall'SCXML
 *
 * @param replyData Dati grezzi della risposta.
 */
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
	_timio->_thread = NULL;
}

/**  MES -> SCXML */
/**
 * @brief Invia una richiesta del MES all'interprete SCXML
 *
 * @param DBid  Il Datablock ID
 * @param cmdid Il TIM cmd ID
 * @param write Lettura/Scrittura
 * @param reqData Lista dei valori fields associati al comando TIM (nel caso di scrittura)
 * @return bool Esito Richiesta
 */
bool XmlBridgeInputEvents::handleMESreq(unsigned int cmdid, unsigned int addr, unsigned int len, bool write, const std::list<std::string> reqData)
{
	if (_invokers.count(len) == 0) {
		LOG(ERROR) << "Command ID not supported by currently active SCXML interpreters and invokers, ignoring MES request";
		LOG(ERROR) << "Fix the CSV";
		return false;
	}
	_invokers[len]->buildMESreq(addr, len, write, reqData);
	return true;
}

/**  TIM -> SCXML */
/**
 * @brief Genera una eccezione per l'ultimo comando inviato dal TIM.
 * @param type Tipo di eccezione
 */
void XmlBridgeInputEvents::handleTIMexception(exceptions type)
{
	std::map<unsigned int, XmlBridgeInvoker*>::const_iterator inviter = _invokers.begin();
	while (inviter != _invokers.end()) {
		inviter->second->buildTIMexception(_timio->_timCmdId.front(), type);
		inviter++;
	}
	if (!_timio->_timCmd.empty()) {
		_timio->_timCmd.pop();
		_timio->_timCmdId.pop();
		_timio->_timCmdWrite.pop();
		_timio->_thread = NULL;
	}
}

} //namespace uscxml
