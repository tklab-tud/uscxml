#ifndef IMINVOKER_H_FNWG0XCQ
#define IMINVOKER_H_FNWG0XCQ

#include <uscxml/Interpreter.h>

//extern "C" {
#include <libpurple/purple.h>
//}
	
#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class IMInvoker : public InvokerImpl {
public:
	struct EventContext {
		InvokeRequest invokeReq;
		SendRequest sendReq;
		IMInvoker* instance;
	};
	
	IMInvoker();
	virtual ~IMInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("im");
		names.insert("instant-messaging");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#instant-messaging");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
	static bool _libPurpleIsInitialized;
	static Data _pluginData;
	static PurpleAccountUiOps _accountUIOps;
	static PurpleEventLoopUiOps _uiEventLoopOps;
	static PurpleCoreUiOps _uiCoreOps;
	static GHashTable* _uiInfo;
	static GRand* _gRand;

	static DelayedEventQueue* _eventQueue;
	
	// these are only being called from the delayed queue's thread
	static void initLibPurple(void *userdata, const std::string event);
	static void send(void *userdata, const std::string event);
	static void invoke(void *userdata, const std::string event);

	// libpurple ui operations
	static guint purpleEventTimeoutAdd(guint interval, GSourceFunc function, gpointer data);
	static gboolean purpleEventTimeoutRemove(guint handle);
	static guint purpleEventInputAdd(int fd, PurpleInputCondition cond, PurpleInputFunction func, gpointer user_data);
	static gboolean purpleEventInputRemove(guint handle);
	static int purpleEventInputGetError(int fd, int *error);
	static guint purpleEventTimeoutAddSec(guint interval, GSourceFunc function, gpointer data);

	// callback contexts
	struct PurpleEventContext {
		PurpleInputFunction input;
		PurpleInputCondition cond;
		int inputFD;
		GSourceFunc function;
		gpointer data;
	};
	static void purpleCallback(void *userdata, const std::string event);
	
	// libpurple core operations
	static void purplePrefsInit(void);
	static void purpleDebugInit(void);
	static void purpleUIInit(void);
	static void purpleQuit(void);
	static GHashTable* purpleGetUIInfo(void);

	// account operations
	static void accountNotifyAdded(PurpleAccount *account,
	                     const char *remote_user,
	                     const char *id,
	                     const char *alias,
	                     const char *message);
	static void accountStatusChanged(PurpleAccount *account,
	                       PurpleStatus *status);
	static void accountRequestAdd(PurpleAccount *account,
	                    const char *remote_user,
	                    const char *id,
	                    const char *alias,
	                    const char *message);
	static void* accountRequestAuthorize(PurpleAccount *account,
	                           const char *remote_user,
	                           const char *id,
	                           const char *alias,
	                           const char *message,
	                           gboolean on_list,
	                           PurpleAccountRequestAuthorizationCb authorize_cb,
	                           PurpleAccountRequestAuthorizationCb deny_cb,
	                           void *user_data);
	static void accountCloseRequest(void *ui_handle);

	
	PurpleAccount* _account;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(IMInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: IMINVOKER_H_FNWG0XCQ */
