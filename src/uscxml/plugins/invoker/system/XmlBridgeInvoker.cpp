/*
 * Use is subject to license terms.
 * Copyright (c) 2013, Ajile di Antonio Iudici. All rights reserved.
 *	<antonio.iudici@ajile.it>
 *	<enrico.papi@ajile.it>
 */

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

/**
 * @brief Distruttore del client TCP
 *
 */
XmlBridgeInvoker::~XmlBridgeInvoker()
{
	LOG(INFO) << "Stopping " << _invokeId;

	if (_servinfo != NULL)
		freeaddrinfo(_servinfo);
	close(_socketfd);
	delete _reply;
}

/**
 * @brief Crea e Registra un Invoker all'interprete SCXML.
 *	Metodo eseguito per ogni elemento <invoke> nell'SCXML
 *
 * @param interpreter	L'interprete chiamante
 * @return boost::shared_ptr<InvokerImpl>	Il puntatore all'invoker.
 */
boost::shared_ptr<InvokerImpl> XmlBridgeInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<XmlBridgeInvoker> ptr = boost::shared_ptr<XmlBridgeInvoker>(new XmlBridgeInvoker());
	return ptr;
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

	/* TODO check integer */
	/* TODO: get all invokers and check for duplicated ids */

	std::string timaddr = _interpreter->getName();
	size_t index = timaddr.find(':');
	_TIMaddr = timaddr.substr(0, index);
	_TIMport = timaddr.substr(index + 1);

	/* Connessione al TIM */
	initClient(_TIMaddr.empty() ? DEF_TIMADDR : _TIMaddr,
		   _TIMport.empty() ? DEF_TIMPORT : _TIMport);

	_CMDid = atoi(_invokeId.substr(sizeof(INVOKER_TYPE)-1).c_str());
	_mesbufferer.registerInvoker(_CMDid, this);
}

/**
 * @brief Non utilizzata
 * @return Data
 */
Data XmlBridgeInvoker::getDataModelVariables() {
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
	SendRequest reqCopy = req;
	std::string evName = reqCopy.getName();
	bool write = (evName.c_str()[0] == WRITEOP);
	std::string evType = evName.substr(1, 3);

	LOG(INFO) << "(" << _invokeId << ") Sending Event " << evName;

	/* I dati inviati dal SCXML all'TIM o al MES sono sempre mappati nella struttura dati 'namelist' dell'evento */
	/* SCXML -> TIM */
	if (evType == SCXML2TIM) {
		//TODO HANDLE MALFORMED SCXML and DATA

		std::stringstream ss;
		std::map<std::string, Data>::const_iterator namelistIter = reqCopy.namelist.begin();
		while(namelistIter != reqCopy.namelist.end()) {
			/* When sending namelist from _datamodel variables, data is interpreted as nodes (data.node) */
			std::map<std::string, Data>::const_iterator nodesIter = namelistIter->second.compound.begin();
			while(nodesIter != namelistIter->second.compound.end()) {
				ss << nodesIter->second.node;
				nodesIter++;
			}
			namelistIter++;
		}

		if (ss.str().empty() || _timeoutVal == 0) {
			buildTIMexception(TIM_ERROR);
			return;
		}

		client(ss.str());

	/* SCXML -> MES */
	} else if (evType == SCXML2MES_ACK) {
		//TODO HANDLE MALFORMED SCXML and DATA

		if (!write) {
			/* When sending namelist from XPath variables, data is interpreted as nodes (data.node) */
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

		if (_itemsRead.size() >= _currItems && !write)
			_mesbufferer.bufferMESreplyREAD(_CMDid, _currAddr, _currLen, _itemsRead);
		else if (write)
			_mesbufferer.bufferMESreplyWRITE(_CMDid);
		else
			LOG(INFO) << "Parsed " << _itemsRead.size() << " fields of " << _currItems << " requested";

	/* SCXML -> MES (errore) */
	} else if (evType == SCXML2MES_ERR) {
		_mesbufferer.bufferMESerror(_CMDid);
	} else {
		LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request\n"
			   << "Propably the event name in the SCXML file is incorrect.";
		_mesbufferer.bufferMESerror(_CMDid);
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
void XmlBridgeInvoker::buildMESreq(unsigned int addr, unsigned int len, bool write,
				   const std::list<std::string> req_raw_data,
				   const std::list<std::pair<std::string,std::string> > req_indexes) {
	std::stringstream ss;
	ss << _CMDid << '_' << (write ? WRITEOP : READOP) << MES2SCXML;
	LOG(INFO) << "(" << _invokeId << ") Building Event " << ss.str();

	Event myevent(ss.str(), Event::EXTERNAL);

	/* I dati inviati dal MES all'SCXML sono sempre mappati nella struttura dati 'node' dell'evento */

	/* Nel caso della lettura vado a scrivere gli indici
	 * Nel caso della scrittura vado a scrivere i valori e gli indici */
	if (!req_indexes.empty() && !req_raw_data.empty() && write) {
		std::list<std::string>::const_iterator valueiter = req_raw_data.begin();
		std::list<std::pair<std::string,std::string> >::const_iterator indexiter = req_indexes.begin();
		myevent.data.node = _interpreter->getDocument().createElement("data");
		for (valueiter; valueiter!= req_raw_data.end(); valueiter++, indexiter++) {
			Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("value");
			Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(*valueiter);
			eventMESElem.setAttribute("index", indexiter->first);
			eventMESElem.setAttribute("var", indexiter->second);
			eventMESElem.appendChild(textNode);
			myevent.data.node.appendChild(eventMESElem);
		}
		_currItems = req_raw_data.size();
	} else if (!req_indexes.empty() && !write) {
		std::list<std::pair<std::string,std::string> >::const_iterator indexiter = req_indexes.begin();
		myevent.data.node = _interpreter->getDocument().createElement("data");
		for (indexiter; indexiter!=req_indexes.end(); indexiter++) {
			Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("index");
			Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(indexiter->second);
			eventMESElem.setAttribute("listid", indexiter->first);
			eventMESElem.appendChild(textNode);
			myevent.data.node.appendChild(eventMESElem);
		}
		_currItems = req_indexes.size();
	} else {
		_currItems = 0;
	}
	_currAddr = addr;
	_currLen = len;
	_currWrite = write;

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
void XmlBridgeInvoker::buildTIMreply(const std::string reply_raw_data)
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
		buildTIMexception(TIM_ERROR);
		return;
	}

	std::stringstream ss;
	ss << _CMDid << '_' << (_currWrite ? WRITEOP : READOP) << TIM2SCXML;

	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		buildTIMexception(TIM_ERROR);
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

/**
 * @brief Attiva una sessione TCP con il server TIM
 * @return Esito operazione
 */
bool XmlBridgeInvoker::connect2TIM() {
	struct addrinfo hints, *p;
	int rv;

	hints.ai_flags = AI_NUMERICHOST;
	hints.ai_family = AF_INET;
	hints.ai_protocol = IPPROTO_TCP;
	hints.ai_socktype = SOCK_STREAM;

	close(_socketfd);
	if (_servinfo != NULL)
		freeaddrinfo(_servinfo);

	if ((rv = getaddrinfo(_TIMaddr.c_str(), _TIMport.c_str(), &hints, &_servinfo)) != 0) {
		PLOG(ERROR) << "Getaddrinfo: " << gai_strerror(rv);
		return false;
	}

	/* loop through all the results and connect to the first we can */
	for (p = _servinfo; p != NULL; p = p->ai_next) {
		if ((_socketfd = socket(p->ai_family, p->ai_socktype,
					p->ai_protocol)) == -1) {
			PLOG(ERROR) << "TIM Client socket()";
			continue;
		}

		struct timeval tv;
		tv.tv_sec = _timeoutVal;
		tv.tv_usec = 0;  // Not init'ing this can cause strange errors
		if (setsockopt(_socketfd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(struct timeval))) {
			PLOG(ERROR) << "TIM Client setting socket options error";
			continue;
		}
		if (setsockopt(_socketfd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(struct timeval))) {
			PLOG(ERROR) << "TIM Client setting socket options error";
			continue;
		}

		if (connect(_socketfd, p->ai_addr, p->ai_addrlen) == -1) {
			close(_socketfd);
			PLOG(INFO) << "TIM Client connect()";
			continue;
		}
		break;
	}

	if (p == NULL) {
		freeaddrinfo(_servinfo);
		close(_socketfd);
		_servinfo = NULL;
		_socketfd = -1;
		return false;
	}

	return true;
}

/**
 * @brief Inizializzazione del Client TCP
 *
 * @param ipaddr
 * @param port
 */
bool XmlBridgeInvoker::initClient(std::string ipaddr, std::string port)
{
	if (ipaddr.empty() || port.empty())
		return false;

	if (!connect2TIM())
		LOG(ERROR) << "TIM Client: failed to connect to " << ipaddr << ":"
			   << port << ". We retry to connect later when a TIM cmd is pending";

	_reply = new char[MAXTIMREPLYSIZE]();
	if (_reply == NULL) {
		close(_socketfd);
		freeaddrinfo(_servinfo);
		LOG(ERROR) << "TIM Client: failed to allocate _reply memory";
		return false;
	}

	return true;
}

/**
 * @brief Invia un comando al TIM. Il comando è ricevuto dall'interprete SCXML.
 *	Immediatamente dopo l'invio attende la risposta del TIM.
 *	Invia un'eventuale risposta all'interprete SCXML.
 *	Tutte le operazioni bloccanti sono interrotte da un timeout.
 *
 * @param Puntatore ad all'istanza di TimIO
 */
void XmlBridgeInvoker::client(std::string cmdframe) {
	if (cmdframe.length() == 0) {
		LOG(ERROR) << "TIM client: sending a 0 length message";
		buildTIMexception(TIM_ERROR);
	}

	LOG(ERROR) << "Sending cmd to TIM (length=" << cmdframe.length() << "): "
		   << std::endl << cmdframe;

	int numbytes;
	while ((numbytes = ::send(_socketfd, cmdframe.c_str(),
				cmdframe.length(), MSG_NOSIGNAL | MSG_MORE)) != cmdframe.length()) {

		PLOG(INFO) << "TIM client: send error";
		if (errno == EPIPE || errno == EBADF) {
			LOG(INFO) << "TCP connection with TCP lost, reconnecting";
			if (!connect2TIM()) {
				buildTIMexception(TIM_ERROR);
				return;
			}
			continue;
		} else if (errno == EAGAIN || errno == EWOULDBLOCK) {
			LOG(ERROR) << "TIM client: command timeout";
			buildTIMexception(TIM_TIMEOUT);
			return;
		}
		buildTIMexception(TIM_ERROR);
		LOG(ERROR) << "TIM client: failed to send";
		return;
	}

	/*
	 * Function blocks until the full amount of message data can be returned
	 */
	size_t replylen = 0;
	memset(_reply, 0, MAXTIMREPLYSIZE);
	do {
		int recvlen;
		if ((recvlen = recv(_socketfd, _reply + replylen,
				    MAXTIMREPLYSIZE - replylen, 0)) == -1) {
			if (errno == EAGAIN || errno == EWOULDBLOCK) {
				LOG(ERROR) << "TIM client: command timeout";
				buildTIMexception(TIM_TIMEOUT);
				return;
			}
			PLOG(ERROR) << "TIM recv error: client ignoring TIM reply";
			buildTIMexception(TIM_ERROR);
			return;
		} else if (recvlen == 0 && errno == 0) {
			LOG(ERROR) << "TIM client: received zero-length message";
			buildTIMexception(TIM_ERROR);
			return;
		} else if (recvlen == (MAXTIMREPLYSIZE - replylen)) {
			LOG(ERROR) << "TIM client: received message too long";
			buildTIMexception(TIM_ERROR);
			return;
		}
		replylen += recvlen;
	} while (std::strncmp(_reply, "<frame>", 7) != 0 ||
		 std::strncmp(&_reply[replylen-8], "</frame>", 8) != 0);

	LOG(ERROR) << "Received reply from TIM: " << std::endl << _reply;

	/* This function logs and reports errors internally */
	buildTIMreply(std::string(_reply));
}

} //namespace uscxml
