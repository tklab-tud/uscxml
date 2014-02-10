/*
 * Use is subject to license terms.
 * Copyright (c) 2013, Ajile di Antonio Iudici. All rights reserved.
 *	<antonio.iudici@ajile.it>
 *	<enrico.papi@ajile.it>
 */

#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <uscxml/Interpreter.h>
#include <glog/logging.h>
#include "uscxml/plugins/invoker/system/timio.h"

#include <map>
#include <iostream>

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

#define DBID_DELIMITER		','

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
	XmlBridgeInvoker() {}
	~XmlBridgeInvoker() {}

	std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		return names;
	}

	boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);
	void send(const SendRequest& req);
	void invoke(const InvokeRequest& req);
	Data getDataModelVariables();

	void buildMESreq(unsigned int addr, unsigned int len, bool write, const std::list<std::string> req_raw_data);
	void buildTIMreply(bool type, const std::string reply_raw_data);
	void buildTIMexception(exceptions type);

protected:
	const unsigned int _CMDid;		/** L'ID del comando gestito dall'invoker */
	const unsigned int _timeoutVal;	/** Il massimo tempo di attesa per ricevere una risposta dal TIM per questo comando */
	unsigned int _currItems;	/** Il numero di items scritti/letti nella richiesta corrent */
	unsigned int _currLen;
	unsigned int _currAddr;

	TimIO* _timio;		/**< Puntatore all'istanza del TIM Client */
	void* _mesbufferer;	/**< Puntatore all'istanze di MesBufferer */

	std::list<std::string> _itemsRead; /** Lista di elementi estratti dalla risposta del TIM tramite query xpath */
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
