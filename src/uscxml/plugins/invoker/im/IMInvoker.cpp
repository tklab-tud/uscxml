#include "IMInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new IMInvokerProvider() );
	return true;
}
#endif

Data IMInvoker::_pluginData;
GHashTable* IMInvoker::_uiInfo = NULL;
GRand* IMInvoker::_gRand = NULL;

PurpleEventLoopUiOps IMInvoker::_uiEventLoopOps =
{
	purpleEventTimeoutAdd,
	purpleEventTimeoutRemove,
	purpleEventInputAdd,
	purpleEventInputRemove,
	purpleEventInputGetError,
	purpleEventTimeoutAddSec,
	
	/* padding */
	NULL,
	NULL,
	NULL
};
	
PurpleAccountUiOps IMInvoker::_accountUIOps = {
	accountNotifyAdded,
	accountStatusChanged,
	accountRequestAdd,
	accountRequestAuthorize,
	accountCloseRequest,
	NULL,
	NULL,
	NULL
};
	
/*** Conversation uiops ***/
static void
null_write_conv(PurpleConversation *conv, const char *who, const char *alias,
								const char *message, PurpleMessageFlags flags, time_t mtime)
{
	const char *name;
	if (alias && *alias)
		name = alias;
	else if (who && *who)
		name = who;
	else
		name = NULL;
	
	printf("(%s) %s %s: %s\n", purple_conversation_get_name(conv),
				 purple_utf8_strftime("(%H:%M:%S)", localtime(&mtime)),
				 name, message);
}

static PurpleConversationUiOps null_conv_uiops =
{
	NULL,                      /* create_conversation  */
	NULL,                      /* destroy_conversation */
	NULL,                      /* write_chat           */
	NULL,                      /* write_im             */
	null_write_conv,           /* write_conv           */
	NULL,                      /* chat_add_users       */
	NULL,                      /* chat_rename_user     */
	NULL,                      /* chat_remove_users    */
	NULL,                      /* chat_update_user     */
	NULL,                      /* present              */
	NULL,                      /* has_focus            */
	NULL,                      /* custom_smiley_add    */
	NULL,                      /* custom_smiley_write  */
	NULL,                      /* custom_smiley_close  */
	NULL,                      /* send_confirm         */
	NULL,
	NULL,
	NULL,
	NULL
};

static void
null_ui_init(void)
{
	/**
	 * This should initialize the UI components for all the modules. Here we
	 * just initialize the UI for conversations.
	 */
	purple_conversations_set_ui_ops(&null_conv_uiops);
}

static PurpleCoreUiOps null_core_uiops =
{
	NULL,
	NULL,
	null_ui_init,
	NULL,
	
	/* padding */
	NULL,
	NULL,
	NULL,
	NULL
};

DelayedEventQueue* IMInvoker::_eventQueue = NULL;

void IMInvoker::initLibPurple(void *userdata, const std::string event) {
	_uiInfo = g_hash_table_new(g_str_hash, g_str_equal);
	_gRand = g_rand_new();
	
	/* Set a custom user directory (optional) */
	//purple_util_set_user_dir(CUSTOM_USER_DIRECTORY);

	/* We do not want any debugging for now to keep the noise to a minimum. */
	purple_debug_set_enabled(false);
	
	purple_core_set_ui_ops(&null_core_uiops);
//	purple_eventloop_set_ui_ops(&glib_eventloops);
	purple_eventloop_set_ui_ops(&_uiEventLoopOps);
	
	purple_plugins_add_search_path("/usr/local/lib/purple-3");
	//		purple_plugins_probe(G_MODULE_SUFFIX);
	
	if (!purple_core_init("uscxml")) {
		LOG(ERROR) << "libpurple initialization failed." << std::endl;
		return;
	}
	
	/* Load the preferences. */
	purple_prefs_load();
	purple_plugins_load_saved("/purple/uscxml/plugins/saved");
	
	GList *l;
	PurplePlugin *plugin;
	
	for (l = purple_plugins_get_all(); l != NULL; l = l->next) {
		plugin = (PurplePlugin *)l->data;
		
		Data pluginData;
		if (plugin->info->id)            pluginData.compound["id"] = Data(plugin->info->id, Data::VERBATIM);
		if (plugin->info->homepage)      pluginData.compound["homepage"] = Data(plugin->info->homepage, Data::VERBATIM);
		if (plugin->info->author)        pluginData.compound["author"] = Data(plugin->info->author, Data::VERBATIM);
		if (plugin->info->description)   pluginData.compound["description"] = Data(plugin->info->description, Data::VERBATIM);
		if (plugin->info->name)          pluginData.compound["name"] = Data(plugin->info->name, Data::VERBATIM);
		if (plugin->info->summary)       pluginData.compound["summary"] = Data(plugin->info->summary, Data::VERBATIM);
		if (plugin->info->version)       pluginData.compound["version"] = Data(plugin->info->version, Data::VERBATIM);
		if (plugin->info->major_version) pluginData.compound["majorVersion"] = Data(toStr(plugin->info->major_version), Data::VERBATIM);
		if (plugin->info->minor_version) pluginData.compound["minorVersion"] = Data(toStr(plugin->info->minor_version), Data::VERBATIM);
		
		if (plugin->info->type == PURPLE_PLUGIN_PROTOCOL)
			_pluginData.compound["protocol"].compound[plugin->info->id] = pluginData;
		
	}

}

void IMInvoker::send(void *userdata, const std::string event) {
	EventContext* ctx = (EventContext*)userdata;
	delete(ctx);
}

static void
signed_on(PurpleConnection *gc, gpointer null)
{
	PurpleAccount *account = purple_connection_get_account(gc);
	printf("Account connected: %s %s\n", purple_account_get_username(account), purple_account_get_protocol_id(account));
}

void IMInvoker::invoke(void *userdata, const std::string event) {
	EventContext* ctx = (EventContext*)userdata;
	IMInvoker* instance = ctx->instance;
	
	std::string username;
	Event::getParam(ctx->invokeReq.params, "username", username);
	std::string protocolId;
	Event::getParam(ctx->invokeReq.params, "protocol", protocolId);
	std::string password;
	Event::getParam(ctx->invokeReq.params, "password", password);

	instance->_account = purple_account_new(username.c_str(), protocolId.c_str());
	purple_account_set_password(instance->_account, password.c_str(), NULL, NULL);
	
	purple_accounts_set_ui_ops(&_accountUIOps);
	
	purple_account_set_enabled(instance->_account, "uscxml", true);
	
	PurpleSavedStatus* status = purple_savedstatus_new(NULL, PURPLE_STATUS_AVAILABLE);
	purple_savedstatus_activate(status);

	int handle;
	purple_signal_connect(purple_connections_get_handle(), "signed-on", &handle,
												PURPLE_CALLBACK(signed_on), NULL);

	delete(ctx);
}

IMInvoker::IMInvoker() {
	_account = NULL;
	if (!_eventQueue) {
		_eventQueue = new DelayedEventQueue();
		_eventQueue->addEvent("initLibPurple", IMInvoker::initLibPurple, 0, NULL);
		_eventQueue->start();
		
		
	}

}

IMInvoker::~IMInvoker() {
	if (_account) {
		purple_account_destroy(_account);
	}
};

boost::shared_ptr<InvokerImpl> IMInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<IMInvoker> invoker = boost::shared_ptr<IMInvoker>(new IMInvoker());
	return invoker;
}

Data IMInvoker::getDataModelVariables() {
	return _pluginData;
}

void IMInvoker::send(const SendRequest& req) {
	EventContext* ctx = new EventContext();
	ctx->sendReq = req;
	ctx->instance = this;
	_eventQueue->addEvent(req.sendid, IMInvoker::invoke, 0, ctx);
	return;
}

void IMInvoker::cancel(const std::string sendId) {
}

void IMInvoker::invoke(const InvokeRequest& req) {
	
	EventContext* ctx = new EventContext();
	ctx->invokeReq = req;
	ctx->instance = this;
	_eventQueue->addEvent(req.sendid, IMInvoker::invoke, 0, ctx);
	return;
}

guint IMInvoker::purpleEventTimeoutAdd(guint interval, GSourceFunc function, gpointer data) {
	PurpleEventContext* ctx = new PurpleEventContext();
	ctx->function = function;
	ctx->input = NULL;
	ctx->data = data;
	uintptr_t ptr = reinterpret_cast<uintptr_t>(ctx);

	_eventQueue->addEvent(toStr(ptr), purpleCallback, interval, ctx);
	return ptr;
}

gboolean IMInvoker::purpleEventTimeoutRemove(guint handle) {
	_eventQueue->cancelEvent(toStr(handle));
	return true;
}

guint IMInvoker::purpleEventTimeoutAddSec(guint interval, GSourceFunc function, gpointer data) {
	return purpleEventTimeoutAdd(interval * 1000, function, data);
}

guint IMInvoker::purpleEventInputAdd(int fd, PurpleInputCondition cond, PurpleInputFunction func, gpointer data) {
	PurpleEventContext* ctx = new PurpleEventContext();
	ctx->function = NULL;
	ctx->input = func;
	ctx->inputFD = fd;
	ctx->cond = cond;
	ctx->data = data;
	
	short opMask = 0;
	if (cond & PURPLE_INPUT_READ)
		opMask |= DelayedEventQueue::FD_READ;
	if (cond & PURPLE_INPUT_WRITE)
		opMask |= DelayedEventQueue::FD_WRITE;
	
	guint eventId = g_rand_int(_gRand);
	_eventQueue->addEvent(toStr(eventId), fd, opMask, purpleCallback, ctx, true);
	return eventId;
}

gboolean IMInvoker::purpleEventInputRemove(guint handle) {
	_eventQueue->cancelEvent(toStr(handle));
	return true;
}

int IMInvoker::purpleEventInputGetError(int fd, int *error) {
	std::cout << "purpleEventInputGetError" << std::endl;
	return 0;
}

void IMInvoker::purpleCallback(void *userdata, const std::string event) {
	PurpleEventContext* ctx = (PurpleEventContext*)userdata;
	if (ctx->function) {
		ctx->function(ctx->data);
		delete ctx;
	} else if(ctx->input) {
		ctx->input(ctx->data, ctx->inputFD, ctx->cond);
	}
}

void IMInvoker::purplePrefsInit(void) {}
void IMInvoker::purpleDebugInit(void) {}
void IMInvoker::purpleUIInit(void) {}
void IMInvoker::purpleQuit(void) {}

GHashTable* IMInvoker::purpleGetUIInfo(void) {
	return _uiInfo;
}

void IMInvoker::accountNotifyAdded(PurpleAccount *account,
																	 const char *remote_user,
																	 const char *id,
																	 const char *alias,
																	 const char *message) {
	std::cout << "accountNotifyAdded" << std::endl;
}

void IMInvoker::accountStatusChanged(PurpleAccount *account,
																		 PurpleStatus *status) {
	std::cout << "accountStatusChanged" << std::endl;

}

void IMInvoker::accountRequestAdd(PurpleAccount *account,
																	const char *remote_user,
																	const char *id,
																	const char *alias,
																	const char *message) {
	std::cout << "accountRequestAdd" << std::endl;
}

void* IMInvoker::accountRequestAuthorize(PurpleAccount *account,
																				const char *remote_user,
																				const char *id,
																				const char *alias,
																				const char *message,
																				gboolean on_list,
																				PurpleAccountRequestAuthorizationCb authorize_cb,
																				PurpleAccountRequestAuthorizationCb deny_cb,
																				void *user_data) {
	// always accept all requests
	authorize_cb(message, user_data);
	return user_data;
}

void IMInvoker::accountCloseRequest(void *ui_handle) {
	std::cout << "accountCloseRequest" << std::endl;
}

	
}