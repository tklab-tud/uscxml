/*
 * Use is subject to license terms.
 * Copyright (c) 2014, Ajile di Antonio Iudici. All rights reserved.
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

static unsigned int timconnCount = 0;
static tthread::mutex timconnMUTEX;
static tthread::condition_variable timconnFLAG;
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
	LOG(INFO) << "Invoking " << _invokeId;

	if (req.params.find("timeout") == req.params.end()) {
		LOG(INFO) << _invokeId << " : no timeout param given, assuming 5 seconds";
		_timeoutVal = 5;
	} else
		_timeoutVal = atoi(req.params.find("timeout")->second.atom.c_str());

	if (_timeoutVal == 0 || _timeoutVal >= 10) {
		LOG(ERROR) << _invokeId << " invalid timeout val";
		exit(EXIT_FAILURE);
	}

	/* TODO: check address errors */
	std::string timaddr = _interpreter->getName();
	size_t index = timaddr.find(':');
	if (index != std::string::npos) {
		_TIMaddr = timaddr.substr(0, index);
		_TIMport = timaddr.substr(index + 1);
	}

	/* TODO: get all invokers and check for duplicated ids */
	_CMDid = atoi(_invokeId.substr(sizeof(INVOKER_TYPE)-1).c_str());
	_mesbufferer.registerInvoker(_CMDid, this);
}

/**
 * @brief Non utilizzata
 * @return Data
 */
Data XmlBridgeInvoker::getDataModelVariables() {
	return Data();
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
	bool iswrite = (evName.c_str()[0] == WRITEOP);
	std::string evType = evName.substr(1, 3);

	LOG(INFO) << "" << _invokeId << " sending event " << evName;

	/* I dati inviati dal SCXML all'TIM o al MES sono sempre mappati nella struttura dati 'namelist' dell'evento */
	/* SCXML -> TIM */
	if (evType == SCXML2TIM) {
		if (!reqCopy.namelist.empty()) {
			std::stringstream ss;
			std::map<std::string, Data>::const_iterator namelistIter = reqCopy.namelist.begin();
			while(namelistIter != reqCopy.namelist.end()) {
				/* When sending namelist from _datamodel variables, data is interpreted as nodes (data.node) */
				std::map<std::string, Data>::const_iterator nodesIter = namelistIter->second.compound.begin();
				while(nodesIter != namelistIter->second.compound.end()) {
					ss << nodesIter->second.node.getNodeValue();
					nodesIter++;
				}
				namelistIter++;
			}

			if (ss.str().empty()) {
				LOG(ERROR) << _invokeId << ": TIM Frame is empty";
				buildTIMexception(SCXML_ERROR);
				return; // <<<<<<<<< RETURN HERE!
			}
			client(ss.str());
		} else if (!reqCopy.xml.empty()) {
			client(reqCopy.xml);
		} else {
			LOG(ERROR) << _invokeId << " cannot create TIM command from send request";
			buildTIMexception(SCXML_ERROR);
		}

		return;  // <<<<<<<<< RETURN HERE!

	/* SCXML -> MES */
	} else if (evType == SCXML2MES_ACK) {

		if (!iswrite) {
			/* Extract parsed TIM reply fields */
			size_t tmpsize = _itemsRead.size();
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
			if (tmpsize == _itemsRead.size()) {
				LOG(ERROR) << _invokeId << ": SCXML have parsed 0 items in this iteration!";
				buildTIMexception(SCXML_ERROR);
				return; // <<<<<<<<< RETURN HERE!;
			}
		}

		if (iswrite) {
			_mesbufferer.bufferMESreplyWRITE(_reqQueue.back()->sock, _CMDid);
		} else {
			if (_itemsRead.size() > _reqQueue.back()->indexes.size()) {
				LOG(ERROR) << _invokeId << " parsed too many fields!";
				buildTIMexception(SCXML_ERROR);
				return; // <<<<<<<<< RETURN HERE!
			} else if (_itemsRead.size() == _reqQueue.back()->indexes.size()) {
				_mesbufferer.bufferMESreplyREAD(_reqQueue.back()->sock, _CMDid,
								_reqQueue.back()->addr,
								_reqQueue.back()->len,
								_itemsRead);
			} else {
				LOG(INFO) << _invokeId << " parsed " << _itemsRead.size() << " fields of "
					  << _reqQueue.back()->indexes.size() << " requested";
				return; // <<<<<<<<< RETURN HERE!
			}
		}

	/* SCXML -> MES (errore) */
	} else if (evType == SCXML2MES_ERR) {
		_mesbufferer.bufferMESerror(_reqQueue.back()->sock, _CMDid);
	} else {
		LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request\n"
			   << "Propably the event name in the SCXML file is incorrect.";
		buildTIMexception(SCXML_ERROR);
		return; // <<<<<<<<< RETURN HERE!
	}

	/* La coda delle richieste all'interno dell'invoker
	 * è mantenuta separatamente da quella presente nella
	 * classe ModbusIO.
	 * Appena l'invoker esegue la chiamata di send per un reply o un errore
	 * la richiesta deve essere rimossa dalla lista */
	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		_reqQueue.pop_back();
		_reqIsNew.pop_back();
	}

	/* Quando la richiesta precedente è stata gestita e rimossa
	   avviamo la macchina a stati con una nuova richiesta
	   Non rischiamo che la richiesta sia gestita due volte siccome
	   usciamo dalla macchina a stati con solo una transizione */
	if (!_reqQueue.empty()) {
		buildMESreq(NULL, false);
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
bool XmlBridgeInvoker::buildMESreq(uscxml::request *myreq, bool newreq) {
	/* verifico la richiesta in ingresso */
	if (newreq && myreq == NULL) {
		LOG(ERROR) << "NULL request received by " << _invokeId;
		return false;
	} else if (newreq && (myreq->sock <= 0 || myreq->len == 0 || (myreq->wdata.empty() && myreq->indexes.empty()) )) {
		LOG(ERROR) << "Invalid request received by " << _invokeId;
		return false;
	}

	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		if (newreq) {
			/* verifico se la coda è piena */
			if (_reqQueue.size() >= _queueSize) {
				LOG(ERROR) << _invokeId << " is currently handling too many requests";
				return false;
			} else if (_reqQueue.size() == 0) {
				_reqIsNew.push_front(true);
			} else if (_reqQueue.size() > 0) {
				_reqIsNew.push_front(false);
			}
			_reqQueue.push_front(myreq);
		} else {
			if (_reqQueue.empty()) {
				LOG(ERROR) << _invokeId << " queue is empty!";
				return false;
			}
		}
	}

	std::stringstream ss;
	ss << _CMDid << '_' << (_reqQueue.back()->write ? WRITEOP : READOP) << MES2SCXML;
	LOG(INFO) << "(" << _invokeId << ") sending event " << ss.str();

	Event myevent(ss.str(), Event::EXTERNAL);

	/* I dati inviati dal MES all'SCXML sono sempre mappati nella struttura dati 'node' dell'evento */
	/* Nel caso della lettura vado a scrivere gli indici
	   Nel caso della scrittura vado a scrivere i valori e gli indici */

	/* TODO CHECK DATA */
	if (_reqQueue.back()->write) {
		/* scrittura */
		std::list<std::string>::const_iterator valueiter = _reqQueue.back()->wdata.begin();
		std::list<std::pair<std::string,std::string> >::const_iterator indexiter = _reqQueue.back()->indexes.begin();
		myevent.data.node = _interpreter->getDocument().createElement("data");
		for (valueiter; valueiter!= _reqQueue.back()->wdata.end(); valueiter++, indexiter++) {
			Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("value");
			Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(*valueiter);
			eventMESElem.setAttribute("itemi", indexiter->first);
			eventMESElem.setAttribute("var", indexiter->second);
			eventMESElem.appendChild(textNode);
			myevent.data.node.appendChild(eventMESElem);
		}
	} else {
		/* lettura */
		std::list<std::pair<std::string,std::string> >::const_iterator indexiter = _reqQueue.back()->indexes.begin();
		myevent.data.node = _interpreter->getDocument().createElement("data");
		for (indexiter; indexiter!=_reqQueue.back()->indexes.end(); indexiter++) {
			Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("index");
			Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(indexiter->second);
			eventMESElem.setAttribute("itemi", indexiter->first);
			eventMESElem.appendChild(textNode);
			myevent.data.node.appendChild(eventMESElem);
		}
	}

	/* elimina le stringhe lette per la richiesta precedente */
	_itemsRead.clear();

	returnEvent(myevent);

	return true;
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
void XmlBridgeInvoker::buildTIMreply(const std::string &reply_raw_data)
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
	ss << _CMDid << '_' << (_reqQueue.back()->write ? WRITEOP : READOP) << TIM2SCXML;

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
	case SCXML_ERROR:
	case TIM_ERROR:
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
 * @brief Invia un comando al TIM. Il comando è ricevuto dall'interprete SCXML.
 *	Immediatamente dopo l'invio attende la risposta del TIM.
 *	Invia un'eventuale risposta all'interprete SCXML.
 *	Tutte le operazioni bloccanti sono interrotte da un timeout.
 *
 * @param Puntatore ad all'istanza di TimIO
 */
void XmlBridgeInvoker::client(const std::string &cmdframe) {

	/* controllo se devo riutilizzare l'xml archiviato del TIM o no */
	if (!_reqIsNew.back()) {
		if (_reply == NULL) {
			LOG(ERROR) << _invokeId << " empty reply buffer, cannot reuse TIM xml data";
			buildTIMexception(TIM_ERROR);
			return;
		}
		LOG(INFO) << _invokeId << " reusing old XML data";
		buildTIMreply(std::string(_reply));
		return;
	} else {
		if (_reply != NULL) {
			delete _reply;
			_reply == NULL;
		}
	}

	if (cmdframe.length() == 0) {
		LOG(ERROR) << _invokeId << " TIM client: sending a 0 length message";
		buildTIMexception(TIM_ERROR);
		return;
	}

	if (_socketfd == -1) {
		tthread::lock_guard<tthread::mutex> timconnlock(timconnMUTEX);
		if (timconnCount >= MAXTIMCONN) {
			timconnFLAG.wait(timconnMUTEX);
			if (timconnCount >= MAXTIMCONN) {
				LOG(ERROR) << _invokeId << " another invoker have not released the connection properly";
				buildTIMexception(TIM_ERROR);
				return;
			}
		}
		if (!connect2TIM()) {
			LOG(ERROR) << "Cannot connect to TIM for sending command";
			buildTIMexception(TIM_ERROR);
			return;
		}
		timconnCount++;
	}

	if (_reply == NULL) {
		_reply = new char[MAXTIMREPLYSIZE]();
		if (_reply == NULL) {
			LOG(ERROR) << "TIM Client: failed to allocate _reply memory";
			buildTIMexception(TIM_ERROR);
			return;
		}
	}

	std::string timframe = std::string("<frame>") + cmdframe.substr(cmdframe.find('>')+1);

	LOG(INFO) << _invokeId << " sending cmd to TIM (length=" << cmdframe.length() << "): "
		   << std::endl << timframe;

	int result = true;
	int numbytes;
	while ((numbytes = ::send(_socketfd, timframe.c_str(),
				  timframe.length(), MSG_NOSIGNAL | MSG_MORE)) != timframe.length()) {

		PLOG(INFO) << "TIM client: send() error";
		if (errno == EPIPE || errno == EBADF) {
			LOG(INFO) << "TCP connection with TCP lost, reconnecting";
			if (!connect2TIM()) {
				LOG(ERROR) << "Cannot reconnect to TIM for sending command";
				buildTIMexception(TIM_ERROR);
				result = false;
				break;
			}
			continue;
		} else if (errno == EAGAIN || errno == EWOULDBLOCK) {
			LOG(ERROR) << "TIM client: command timeout";
			buildTIMexception(TIM_TIMEOUT);
			result = false;
			break;
		}
		buildTIMexception(TIM_ERROR);
		result = false;
		break;
	}

	/*
	 * Function blocks until the full amount of message data can be returned
	 */
	if (result) {
		size_t replylen = 0;
		do {
			int recvlen;
			if ((recvlen = recv(_socketfd, _reply + replylen,
					    MAXTIMREPLYSIZE - replylen, 0)) == -1) {
				if (errno == EAGAIN || errno == EWOULDBLOCK) {
					PLOG(ERROR) << "TIM client: command timeout";
					buildTIMexception(TIM_TIMEOUT);
					result = false;
					break;
				}
				PLOG(ERROR) << "TIM recv error: client ignoring TIM reply";
				buildTIMexception(TIM_ERROR);
				result = false;
				break;
			} else if (recvlen == 0 && errno == 0) {
				PLOG(ERROR) << "TIM client: received zero-length message";
				buildTIMexception(TIM_ERROR);
				result = false;
				break;
			} else if (recvlen == (MAXTIMREPLYSIZE - replylen)) {
				PLOG(ERROR) << "TIM client: received message too long";
				buildTIMexception(TIM_ERROR);
				result = false;
				break;
			}
			replylen += recvlen;
		} while (std::strncmp(_reply, "<frame>", 7) != 0 ||
			 std::strncmp(&_reply[replylen-8], "</frame>", 8) != 0);
	}

	if (result) {
		LOG(INFO) << _invokeId << " received reply from TIM: " << std::endl << _reply;
		/* This function logs and reports errors internally */
		buildTIMreply(std::string(_reply));
	}

	{
		tthread::lock_guard<tthread::mutex> timconnlock(timconnMUTEX);
		if (timconnCount >= MAXTIMCONN) {
			if (close(_socketfd)) {
				LOG(ERROR) << "Error closing socket " << _socketfd;
			}
			_socketfd = -1;
			timconnCount--;
			timconnFLAG.notify_all();
		}
	}
}

} //namespace uscxml
