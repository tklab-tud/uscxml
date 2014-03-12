/*
 * Use is subject to license terms.
 * Copyright (c) 2014, Ajile di Antonio Iudici. All rights reserved.
 *	<antonio.iudici@ajile.it>
 *	<enrico.papi@ajile.it>
 */

#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <uscxml/Interpreter.h>
#include <glog/logging.h>
#include <sys/socket.h>
#include <netdb.h>
#include <mesbufferer.h>
#include <ctime>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

#define READOP			'r'
#define WRITEOP			'w'

#define SCXML2TIM		"CMD"
#define SCXML2MES_ACK		"ACK"
#define SCXML2MES_ERR		"ERR"

#define MES2SCXML		"REQ"
#define TIM2SCXML		"REPLY"

#define TIM2SCXML_TIMEOUT	"timeout"
#define TIM2SCXML_ERROR		"error"

#define INVOKER_TYPE		"xmlbridge"

#define MAXTIMREPLYSIZE		20000           /**< Lunghezza del buffer di ricezione delle risposte TIM */
#define DEF_TIMADDR		"127.0.0.1"     /**< Indirizzo su cui il sistema TIM è in ascolto */
#define DEF_TIMPORT		"3000"          /**< Porta su cui il sistema TIM è in ascolto */

#define MAXTIMCONN		6   /**< Massimo numero di connessioni che può gestire il sistema TIM */
#define MAXQUEUEDELAY		2   /**< Tempo massimo per cui una risposta del TIM può essere riutilizzata per le richieste successive */
#define MAXQUEUESIZE		5   /**< Massimo numero di richiesta che posso accodare per un comando TIM */
#define MAXTIMCONNDELAY		5

/**
 * @brief Enum che elenca i tipi di eccezzione che l'invoker può generare
 */
enum exceptions {
	TIM_TIMEOUT,        /**< La comunicazione di rete col TIM è andata in timeout */
	TIM_ERROR,          /**< I dati inviati/ricevuto al/dal TIM hanno generato un errore */
	SCXML_ERROR         /**< L'SCXML non è correttamente specificato */
};

/**
  * @brief Struttura di una richiesta ricevuta e gestita dell'invoker
  */
struct request {
	int sock;               /**< Socket TCP lato modbus sul quale la richiesta è pervenuta */
	unsigned int addr;      /**< Modbus starting address */
	unsigned int len;       /**< Lunghezza complessiva dei dati richesti via modbus */
	bool write;             /**< Richiesta in scrittura/lettura */
	std::list<std::string> wdata;   /**< Lista di stringhe da scrivere nel TIM */
	std::list<std::pair<std::string,std::string> > indexes; /**< Elenco di indice e nome variabile dei nodi XML della risposta TIM, per ogni field richiesto via modbus */
};

/**
 * @brief Implementa un generico USCXML Invoker che gestisce eventi SCXML esterni/interni appartenenti ad un dato commando TIM
 */
class XmlBridgeInvoker : public InvokerImpl {
public:
	XmlBridgeInvoker() :
		_timeoutVal(MAXTIMCONNDELAY), _queueSize(MAXQUEUESIZE),
		_itemsRead(), _mesbufferer(MesBufferer::getInstance()),
		_TIMport(DEF_TIMPORT), _TIMaddr(DEF_TIMADDR),
		_reply(NULL),  _socketfd(-1), _servinfo(NULL),
		_reqQueue(), _reqClock(),  _lastWrite(false) {}

	std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);
	void send(const SendRequest& req);
	void invoke(const InvokeRequest& req);
	Data getDataModelVariables();

	bool buildMESreq(request *myreq, bool newreq);
	void buildTIMreply(const char *reply_raw_data);
	void buildException(exceptions type);

	~XmlBridgeInvoker();

protected:
	void client(const std::string &cmdframe);
	bool connect2TIM();

	/* FIXED */
	unsigned int _CMDid;		/** L'ID del comando TIM gestito dall'invoker */
	unsigned int _timeoutVal;	/** Il massimo tempo di attesa per le comunicazioni di rete lato TIM */
	unsigned int _queueSize;	/** Massimo numero di richieste accodate nell'invoker */

	std::list<std::string> _itemsRead;	/** Lista di elementi estratti dalla risposta XML del TIM tramite query xpath per un comando di lettura*/

	MesBufferer& _mesbufferer;	/**< Puntatore all'istanza di MesBufferer */

	std::string _TIMport;		/**< Porta TCP del server TIM */
	std::string _TIMaddr;		/**< Indirizzo del server TIM */
	char* _reply;			/**< Buffer di ricezione del client TIM */
	int _socketfd;			/**< Socket descriptor del client TIM */
	struct addrinfo *_servinfo;	/**< Informazioni di sessione del server TIM */

	std::list<request *> _reqQueue;   /**< Lista di richieste arrivate all'invoker. La prima è la più recente, l'ultima è quella gestita attualmente */
	std::list<std::clock_t> _reqClock;  /**< Lista del tempi di arrivo (espressi in clock di sistema) per tutte le richieste accodate. Le richieste giunte a coda vuota hanno il val. impostato a 0 */
	bool _lastWrite;                    /**< Indica se l'ultima richiesta gestita era in lettura */

	tthread::mutex queueMUTEX;          /**< Mutex di accesso alla coda delle richieste */
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
