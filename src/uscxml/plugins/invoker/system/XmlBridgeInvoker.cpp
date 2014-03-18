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

static unsigned int timconnCount = 0;   /**< Contatore statico delle connessioni attualmente attive lato TIM */
static tthread::mutex timconnMUTEX;     /**< Mutex che controlla l'accesso al contatore delle connessioni */
static tthread::condition_variable timconnFLAG;     /**< Condition variable per sincronizzare l'acquisizione e rilascio di socket lato TIM */

/**
 * @brief Distruttore della classe XmlBridgeInvoker
 */
XmlBridgeInvoker::~XmlBridgeInvoker()
{
	LOG(INFO) << "Stopping " << _invokeId;

	if (!_reqQueue.empty()) {
		std::list<request *>::const_iterator reqiter;
		for (reqiter = _reqQueue.begin(); reqiter != _reqQueue.end(); reqiter++)
			delete (*reqiter);
	}
	if (_servinfo != NULL)
		freeaddrinfo(_servinfo);
	close(_socketfd);
	delete _reply;
}

/**
 * @brief Alloca e Registra un Invoker nell'interprete SCXML.
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
 * @param req La richiesta specificata nell'elemento <send> dell'SCXML
 */
void XmlBridgeInvoker::send(const SendRequest& req) {
	LOG(INFO) << "" << _invokeId << " sending event " << req.name;

	/* I dati inviati dal SCXML all'TIM o al MES sono sempre mappati nella struttura dati 'namelist' dell'evento */

	/* Questa routine deve essere ottimizzata per eseguire più velocemente il caso SCXML2MES_ACK in lettura */

	/* SCXML -> MES */
	if (req.name.substr(1, 3) == SCXML2MES_ACK) {
		/* READ */
		if (req.name.c_str()[0] != WRITEOP) {
			/* Extract parsed TIM reply fields */
			size_t tmpsize = _itemsRead.size();
			/* When sending namelist from XPath variables, data is interpreted as nodes (data.node) */
			std::map<std::string, Data>::const_iterator namelistIter = req.namelist.begin();
			while(namelistIter != req.namelist.end()) {
				std::map<std::string, Data>::const_iterator nodesIter = namelistIter->second.compound.begin();
				while(nodesIter != namelistIter->second.compound.end()) {
					_itemsRead.push_back(nodesIter->second.node.getNodeValue());
					nodesIter++;
				}
				namelistIter++;
			}
			if (tmpsize == _itemsRead.size()) {
				LOG(ERROR) << _invokeId << ": SCXML have parsed 0 items in this iteration!";
				buildException(SCXML_ERROR);
				return; // <<<<<<<<< RETURN HERE!;
			}
			if (_itemsRead.size() > _reqQueue.back()->indexes.size()) {
				LOG(ERROR) << _invokeId << " parsed too many fields!";
				buildException(SCXML_ERROR);
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
		/* WRITE */
		} else {
			_mesbufferer.bufferMESreplyWRITE(_reqQueue.back()->sock, _CMDid);
		}
	/* SCXML -> TIM */
	} else if (req.name.substr(1, 3) == SCXML2TIM) {
		if (!req.namelist.empty()) {
			std::stringstream ss;
			std::map<std::string, Data>::const_iterator namelistIter = req.namelist.begin();
			while(namelistIter != req.namelist.end()) {
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
				buildException(SCXML_ERROR);
				return; // <<<<<<<<< RETURN HERE!
			}
			client(ss.str());
		} else if (!req.xml.empty()) {
			client(req.xml);
		} else {
			LOG(ERROR) << _invokeId << " cannot create TIM command from send request";
			buildException(SCXML_ERROR);
		}

		return;  // <<<<<<<<< RETURN HERE!

	} else if (req.name.substr(1, 3) == SCXML2MES_ERR) {
		_mesbufferer.bufferMESerror(_reqQueue.back()->sock, _CMDid);
	} else {
		LOG(ERROR) << "XmlBridgeInvoker: received an unsupported event type from Interpreter, discarding request\n"
			   << "Propably the event name in the SCXML file is incorrect.";
		buildException(SCXML_ERROR);
		return; // <<<<<<<<< RETURN HERE!
	}

	/* La coda delle richieste all'interno dell'invoker
	 * è mantenuta separatamente da quella presente nella
	 * classe ModbusIO.
	 * Appena l'invoker esegue la chiamata di send per un reply o un errore
	 * la richiesta deve essere rimossa dalla lista */
	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		delete _reqQueue.back();
		_reqQueue.pop_back();
		_reqClock.pop_back();
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
 * @param myreq     La richiesta in ingresso
 * @param newreq	Indica se si deve analizzare la richiesta presente nel parametro 'myreq' o processare le richieste in coda
 */
bool XmlBridgeInvoker::buildMESreq(request *myreq, bool newreq) {
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
				/* Se la richiesta è la prima ad essere accodata deve sempre
				 * forzare la connessione al TIM */
				_reqClock.push_front(0);
			} else if (_reqQueue.size() > 0) {
				LOG(INFO) << _invokeId << " queueing request on socket #" << myreq->sock;
				_reqClock.push_front(std::clock());
			}
			_reqQueue.push_front(myreq);
		} else {
			/* Se richiedo di analizzare richieste già esistenti
			 * si suppone che la coda non sia vuota */
			if (_reqQueue.empty()) {
				LOG(ERROR) << _invokeId << " queue is empty!";
				return false;
			}
		}
	}

	Event myevent;

	{
		std::stringstream ss;
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		ss << _CMDid << '_' << (_reqQueue.back()->write ? WRITEOP : READOP) << MES2SCXML;
		LOG(INFO) << _invokeId << " sending event " << ss.str();
		myevent.name = ss.str();
		myevent.eventType = Event::EXTERNAL;
		myevent.hideSendId = false;

		/* I dati inviati dal MES all'SCXML sono sempre mappati nella struttura dati 'node' dell'evento */
		/* Nel caso della lettura vado a scrivere gli indici
		   Nel caso della scrittura vado a scrivere i valori e gli indici */

		if (_reqQueue.back()->write) {
			/* scrittura */
			std::list<std::string>::const_iterator valueiter;
			std::list<std::pair<std::string,std::string> >::const_iterator indexiter;
			myevent.data.node = _interpreter->getDocument().createElement("data");
			for (valueiter = _reqQueue.back()->wdata.begin(), indexiter = _reqQueue.back()->indexes.begin();
			     valueiter!= _reqQueue.back()->wdata.end();
			     valueiter++, indexiter++) {
				Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("value");
				Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(*valueiter);
				eventMESElem.setAttribute("itemi", indexiter->first);
				eventMESElem.setAttribute("var", indexiter->second);
				eventMESElem.appendChild(textNode);
				myevent.data.node.appendChild(eventMESElem);
			}
		} else {
			/* lettura */
			std::list<std::pair<std::string,std::string> >::const_iterator indexiter;
			myevent.data.node = _interpreter->getDocument().createElement("data");
			for (indexiter = _reqQueue.back()->indexes.begin();
			     indexiter!=_reqQueue.back()->indexes.end(); indexiter++) {
				Arabica::DOM::Element<std::string> eventMESElem = _interpreter->getDocument().createElement("index");
				Arabica::DOM::Text<std::string> textNode = _interpreter->getDocument().createTextNode(indexiter->second);
				eventMESElem.setAttribute("itemi", indexiter->first);
				eventMESElem.appendChild(textNode);
				myevent.data.node.appendChild(eventMESElem);
			}
		}
	}

	/* elimina le stringhe lette per la richiesta precedente */
	_itemsRead.clear();

	returnEvent(myevent);

	return true;
}

/** TIM->SCXML */
/**
 * @brief Effettua il parsing di una risposta XML inviato dal TIM verso il gateway.
 *	Genera un evento SCXML con la struttura dati risultante
 *
 * @param reply_raw_data Buffer dati in ricezione dal TIM
 */
void XmlBridgeInvoker::buildTIMreply(const char *reply_raw_data)
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
		buildException(TIM_ERROR);
		return;
	}

	std::stringstream ss;
	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		ss << _CMDid << '_' << (_reqQueue.back()->write ? WRITEOP : READOP) << TIM2SCXML;
	}


	Event myevent(ss.str(), Event::EXTERNAL);
	if (!domParser.getDocument().hasChildNodes()) {
		LOG(ERROR) << "Failed parsing TIM XML reply. Resulting document has no nodes";
		buildException(TIM_ERROR);
		return;
	}

	/* I dati inviati dal SCXML all'SCXML sono sempre mappati nella struttura dati 'dom' dell'evento */
	myevent.dom = domParser.getDocument().getDocumentElement();

	LOG(INFO) << _invokeId << " sending event " << ss.str();

	returnEvent(myevent);
}

/** TIM->SCXML */
/**
 * @brief Segnala all'SCXML che l'invoker ha generato un'eccezione.
 *
 * @param type Tipo di eccezione
 */
void XmlBridgeInvoker::buildException(exceptions type)
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
 * @brief Invia un messaggio al TIM contenente un comando di scrittura/lettura.
 *	Immediatamente dopo l'invio attende la risposta del TIM.
 *	Invia un'eventuale risposta all'interprete SCXML.
 *	Tutte le operazioni bloccanti sono interrotte da un timeout.
 *
 * @param cmdframe Reference alla stringa da inviare al TIM
 */
void XmlBridgeInvoker::client(const std::string &cmdframe) {

	/* controllo se devo riutilizzare l'xml archiviato del TIM o no */
	bool reuse;
	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		reuse = (_reqClock.back() != 0 && !_reqQueue.back()->write && !_lastWrite &&
			((std::clock() - _reqClock.back()) < (MAXQUEUEDELAY * CLOCKS_PER_SEC)));
	}

	if (reuse) {
		if (_reply == NULL || _reply[0] == '\0' || std::strncmp(_reply, "<frame>", 7)) {
			LOG(ERROR) << _invokeId << " empty reply buffer, cannot reuse TIM xml data";
			buildException(TIM_ERROR);
			return;  // <<<<< Return Here!
		}
		LOG(INFO) << _invokeId << " reusing old TIM reply!";
		buildTIMreply(_reply);
		return;  // <<<<< Return Here!
	}

	if (cmdframe.length() == 0) {
		LOG(ERROR) << _invokeId << " TIM client: sending a 0 length message";
		buildException(TIM_ERROR);
		return;
	}

	if (_socketfd == -1) {
		LOG(INFO) << _invokeId << " connecting to TIM";
		tthread::lock_guard<tthread::mutex> timconnlock(timconnMUTEX);
		if (timconnCount >= MAXTIMCONN) {
			timconnFLAG.wait(timconnMUTEX);
			if (timconnCount >= MAXTIMCONN) {
				LOG(ERROR) << _invokeId << " another invoker have not released the connection properly";
				buildException(TIM_ERROR);
				return;
			}
		}
		if (!connect2TIM()) {
			LOG(ERROR) << "Cannot connect to TIM for sending command";
			buildException(TIM_ERROR);
			return;
		}
		timconnCount++;
	}

	if (_reply == NULL) {
		_reply = new char[MAXTIMREPLYSIZE]();
		if (_reply == NULL) {
			LOG(ERROR) << "TIM Client: failed to allocate _reply memory";
			buildException(TIM_ERROR);
			return;
		}
	}

	std::string timframe = std::string("<frame>") + cmdframe.substr(cmdframe.find('>')+1);

	LOG(INFO) << _invokeId << " sending cmd to TIM (length=" << cmdframe.length() << "): "
		  << std::endl << timframe;

	bool result = true;
	int numbytes;
	while ((numbytes = ::send(_socketfd, timframe.c_str(),
				  timframe.length(), MSG_NOSIGNAL | MSG_MORE)) != timframe.length()) {

		PLOG(INFO) << "TIM client: send() error";
		if (errno == EPIPE || errno == EBADF) {
			LOG(INFO) << "TCP connection with TCP lost, reconnecting";
			if (!connect2TIM()) {
				LOG(ERROR) << "Cannot reconnect to TIM for sending command";
				buildException(TIM_ERROR);
				result = false;
				break;
			}
			continue;
		} else if (errno == EAGAIN || errno == EWOULDBLOCK) {
			LOG(ERROR) << "TIM client: command timeout";
			buildException(TIM_TIMEOUT);
			result = false;
			break;
		}
		buildException(TIM_ERROR);
		result = false;
		break;
	}

	/*
	 * Function blocks until the full amount of message data can be returned
	 */
	if (result) {
		size_t replylen = 0;
		if (_reply[0] != '\0')
			std::memset(_reply, 0, MAXTIMREPLYSIZE);
		do {
			int recvlen;
			if ((recvlen = recv(_socketfd, _reply + replylen,
					    MAXTIMREPLYSIZE - replylen, 0)) == -1) {
				if (errno == EAGAIN || errno == EWOULDBLOCK) {
					PLOG(ERROR) << "TIM client: command timeout";
					buildException(TIM_TIMEOUT);
					result = false;
					break;
				}
				PLOG(ERROR) << "TIM recv error: client ignoring TIM reply";
				buildException(TIM_ERROR);
				result = false;
				break;
			} else if (recvlen == 0 && errno == 0) {
				PLOG(ERROR) << "TIM client: received zero-length message";
				buildException(TIM_ERROR);
				result = false;
				break;
			} else if (recvlen == (MAXTIMREPLYSIZE - replylen)) {
				PLOG(ERROR) << "TIM client: received message too long";
				buildException(TIM_ERROR);
				result = false;
				break;
			}
			replylen += recvlen;
		} while (std::strncmp(_reply, "<frame>", 7) != 0 ||
			 std::strncmp(&_reply[replylen-8], "</frame>", 8) != 0);
	}

	{
		tthread::lock_guard<tthread::mutex> queuelock(queueMUTEX);
		if (_reqQueue.back()->write) {
			_lastWrite = true;
		} else {
			_lastWrite = false;
		}
	}

	if (result) {
		LOG(INFO) << _invokeId << " received reply from TIM: " << std::endl << _reply;
		/* This function logs and reports errors internally */
		buildTIMreply(_reply);
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
