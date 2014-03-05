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

#define MAXCONN			5

enum exceptions {
	TIM_TIMEOUT,
	TIM_ERROR,
	SCXML_ERROR
};

/**
 * @brief Implementa un generico USCXML Invoker che gestisce eventi SCXML esterni/interni appartenenti ad un dato datablock
 */
class XmlBridgeInvoker : public InvokerImpl {
public:
    XmlBridgeInvoker() : currSock(-1), _reply(NULL), _servinfo(NULL), _socketfd(-1),
        _itemsRead(), _mesbufferer(MesBufferer::getInstance()),
		_currAddr(-1), _currItems(0), _currLen(0), _currWrite(false) {}
	std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);
	void send(const SendRequest& req);
	void invoke(const InvokeRequest& req);
	Data getDataModelVariables();

    bool buildMESreq(int sock, unsigned int addr, unsigned int len, bool write, const std::list<std::string> &req_raw_data,
                                    const std::list<std::pair<std::string, std::string> > &req_indexes);
	void buildTIMreply(const std::string &reply_raw_data);
	void buildTIMexception(exceptions type);

	~XmlBridgeInvoker();
protected:    
	bool initClient(std::string ipaddr, std::string port);
	void client(const std::string &cmdframe);
	bool connect2TIM();

	unsigned int _CMDid;		/** L'ID del comando gestito dall'invoker */
	unsigned int _timeoutVal;	/** Il massimo tempo di attesa per ricevere una risposta dal TIM per questo comando */
	unsigned int _currItems;	/** Il numero di items scritti/letti nella richiesta corrent */
	unsigned int _currLen;
	int _currAddr;
	bool _currWrite;

    int currSock;
    tthread::mutex sockMUTEX;

	std::list<std::string> _itemsRead;	/** Lista di elementi estratti dalla risposta del TIM tramite query xpath */

	MesBufferer& _mesbufferer;	/**< Puntatore all'istanze di MesBufferer */

	std::string _TIMport;		/**< Porta TCP del server TIM */
	std::string _TIMaddr;		/**< Indirizzo del server TIM */
	char* _reply;			/**< Buffer di ricezione del client TIM */
	int _socketfd;			/**< Socket descriptor del client TIM */
	struct addrinfo *_servinfo;	/**< Informazioni di sessione del server TIM */
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
