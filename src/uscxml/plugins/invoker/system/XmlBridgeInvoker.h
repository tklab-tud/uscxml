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

#define MAXTIMREPLYSIZE		20000
#define DEF_TIMADDR		"127.0.0.1"
#define DEF_TIMPORT		"3000"

#define MAXTIMCONN		6

enum exceptions {
	TIM_TIMEOUT,
	TIM_ERROR,
	SCXML_ERROR
};

typedef struct request {
	int sock;
	unsigned int addr;
	unsigned int len;
	bool write;
	std::list<std::string> wdata;
	std::list<std::pair<std::string,std::string> > indexes;
} request_t;

/**
 * @brief Implementa un generico USCXML Invoker che gestisce eventi SCXML esterni/interni appartenenti ad un dato datablock
 */
class XmlBridgeInvoker : public InvokerImpl {
public:
	XmlBridgeInvoker() :
		_reply(NULL), _servinfo(NULL), _socketfd(-1),
		_itemsRead(), _mesbufferer(MesBufferer::getInstance()),
		_reqQueue(), _queueSize(5),
		_TIMaddr(DEF_TIMADDR), _TIMport(DEF_TIMPORT) {}

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
	void buildTIMreply(const std::string &reply_raw_data);
	void buildTIMexception(exceptions type);

	~XmlBridgeInvoker();

protected:
	void client(const std::string &cmdframe);
	bool connect2TIM();

	/* FIXED */
	unsigned int _CMDid;		/** L'ID del comando gestito dall'invoker */
	unsigned int _timeoutVal;	/** Il massimo tempo di attesa per ricevere una risposta dal TIM per questo comando */
	unsigned int _queueSize;	/** Massimo numero di richieste parallele accodate per comando */

	std::list<std::string> _itemsRead;	/** Lista di elementi estratti dalla risposta del TIM tramite query xpath */

	MesBufferer& _mesbufferer;	/**< Puntatore all'istanze di MesBufferer */

	std::string _TIMport;		/**< Porta TCP del server TIM */
	std::string _TIMaddr;		/**< Indirizzo del server TIM */
	char* _reply;			/**< Buffer di ricezione del client TIM */
	int _socketfd;			/**< Socket descriptor del client TIM */
	struct addrinfo *_servinfo;	/**< Informazioni di sessione del server TIM */

	std::list<request *> _reqQueue;
	std::list<bool> _reqIsNew;
	bool isNewReq;

	tthread::mutex queueMUTEX;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
