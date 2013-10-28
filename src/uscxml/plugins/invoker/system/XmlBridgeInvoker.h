#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <map>
#include <iostream>

#include <uscxml/Interpreter.h>
#include <glog/logging.h>
#include "uscxml/plugins/invoker/system/timio.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

#define READOP			'r'
#define WRITEOP			'w'

#define SCXML2TIM		"Cmd"
#define SCXML2MES_ACK		"Ack"
#define SCXML2MES_ERR		"Err"

#define MES2SCXML		"Req"
#define TIM2SCXML		"Reply"

#define TIM2SCXML_TIMEOUT	"timeout"
#define TIM2SCXML_ERROR		"error"

#define INVOKER_TYPE		"xmlbridge"

#define DBID_DELIMITER		','

enum exceptions {
	TIM_TIMEOUT,
	TIM_ERROR,
	SCXML_ERROR
};

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

	void buildMESreq(unsigned int cmdid, bool write, const std::list<std::string> req_raw_data);
	void buildTIMreply(unsigned int cmdid, bool type, const std::string reply_raw_data);
	void buildTIMexception(unsigned int cmdid, exceptions type);

protected:
	unsigned int _DBid;		/** L'ID del datablock gestito dall'invoker */
	unsigned int _timeoutVal;	/** Il Timeout di default da applicare per le comunicazioni col TIM */
};

class XmlBridgeInputEvents {
public:
	~XmlBridgeInputEvents() {
		// call all the invokers and send event to final
	}

	void sendReq2TIM(unsigned int cmdid, bool write, const std::string reqData, unsigned int timeout);
	void sendReply2MES(unsigned int DBid, unsigned int cmdid, bool write, const std::string replyData);
	void sendErr2MES(unsigned int DBid, unsigned int cmdid);

	void handleTIMreply(const std::string replyData);
	void handleTIMexception(exceptions type);
	bool handleMESreq(unsigned int DBid, unsigned int cmdid, bool write, const std::list<std::string> reqData);

	/**
	 * @brief Registra un invoker
	 * @param Puntatore all'istanza
	 */
	void registerInvoker(unsigned int DBid, XmlBridgeInvoker* invokref) {
		_invokers.insert(std::pair<unsigned int, XmlBridgeInvoker* >(DBid, invokref));
	}
	/**
	 * @brief Registra una istanza di TimIO
	 * @param Puntatore all'istanza
	 */
	void registerTimio(TimIO* ioref) {
		_timio = ioref;
	}

	/**
	 * @brief Registra una istanza di MesBufferer
	 * @param Puntatore all'istanza
	 */
	void registerMesbufferer(void* mesref) {
		_mesbufferer = mesref;
	}

	/**
	 * @brief Ritorna una reference all'istanza del singleton XmlBridgeInputEvents
	 *	Se l'oggetto statico non è ancora stato creato, istanzia la classe.
	 * @return La reference di XmlBridgeInputEvents
	 */
	static XmlBridgeInputEvents& getInstance() {
		static XmlBridgeInputEvents instance;
		return instance;
	}

private:
	/**
	 * @brief Istanzia il Singleton XmlBridgeInputEvents
	 */
	XmlBridgeInputEvents() : _invokers() {
		LOG(INFO) << "Instantiating XmlBridgeInputEvents Singleton";
	}
	XmlBridgeInputEvents& operator=( const XmlBridgeInputEvents& );

	/** Mappa che ha per indice l'id di un datablock e per contenuto
	 * il puntatore all'invoker che lo gestisce.
	 * Esiste un invoker per ciascun datablock specificato nel nome della macchina a stati SCXML */
	std::map<unsigned int, XmlBridgeInvoker*> _invokers;

	TimIO* _timio;		/**< Puntatore all'istanza del TIM Client */
	void* _mesbufferer;	/**< Puntatore all'istanze di MesBufferer */
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
