#include "IMInvoker.h"
#include <glog/logging.h>
#include "uscxml/UUID.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define GET_INSTANCE_IN_CALLBACK(account) \
tthread::lock_guard<tthread::mutex> lock(_accountMutex); \
if (_accountInstances.find(account) == _accountInstances.end()) { \
	LOG(ERROR) << "Callback for unknown account called"; \
	return; \
} \
IMInvoker* inst = _accountInstances[account];\


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
	NULL, //purpleEventInputGetError,
	purpleEventTimeoutAddSec,
	NULL,
	NULL,
	NULL
};
	
PurpleAccountUiOps IMInvoker::_uiAccountOps = {
	accountNotifyAdded,
	accountStatusChanged,
	accountRequestAdd,
	accountRequestAuthorize,
	accountCloseRequest,
	NULL,
	NULL,
	NULL
};

PurpleBlistUiOps IMInvoker::_uiBuddyOps = {
	purpleNewList,
	purpleNewNode,
	purpleShow,
	NULL, // purpleUpdate,
	NULL, // purpleRemove,
	NULL, // purpleDestroy,
	NULL, // purpleSetVisible,
	purpleRequestAddBuddy,
	purpleRequestAddChat,
	purpleRequestAddGroup,
	NULL, // purpleSaveNode,
	NULL, // purpleRemoveNode,
	NULL, // purpleSaveAccount,
};

// file transfer
PurpleXferUiOps IMInvoker::_uiXferOps = {
	purpleNewXfer,
	purpleDestroy,
	purpleAddXfer,
	purpleUpdateProgress,
	purpleCancelLocal,
	purpleCancelRemote,
	purpleWrite,
	purpleRead,
	purpleDataNotSent,
	purpleAddThumbnail
};

// connection info
PurpleConnectionUiOps IMInvoker::_uiConnectOps = {
	purpleConnectProgress,
	purpleConnected,
	purpleDisonnected,
	purpleNotice,
	purpleNetworkConnected,
	purpleNetworkDisconnected,
	purpleReportDisconnect,
	NULL,
	NULL,
	NULL

};

//libpurple conversation operations
PurpleConversationUiOps IMInvoker::_uiConvOps =
{
	NULL, //purpleCreateConversation,
	NULL, //purpleDestroyConversation,
	NULL, //purpleWriteChat,
	NULL, //purpleWriteIm,
	purpleWriteConv,
	NULL, //purpleChatRenameUser,
	NULL, //purpleChatRemoveUsers,
	NULL, //purpleChatUpdateUser,
	NULL, //purplePresentConversation,
	NULL, //purpleHasFocus,
	NULL, //purpleCustomSmileyAdd,
	NULL, //purpleCustomSmileyWrite,
	NULL, //purpleCustomSmileyClose,
	NULL, //purpleSendConfirm,
	NULL,
	NULL,
	NULL,
	NULL
};

PurpleNotifyUiOps IMInvoker::_uiNotifyOps = {
	purpeNotifyMessage,
	purpeNotifyEmail,
	purpeNotifyEmails,
	purpeNotifyFormatted,
	purpeNotifySearchResults,
	purpeNotifySearchResultsNewRows,
	purpeNotifyUserInfo,
	purpeNotifyURI,
	purpeNotifyClose,
	NULL,
	NULL,
	NULL,
	NULL
};

PurplePrivacyUiOps IMInvoker::_uiPrivacyOps = {
	purplePermitAdded,
	purplePermitRemoved,
	purpleDebyAdded,
	purpleDenyRemoved,
	NULL,
	NULL,
	NULL,
	NULL
};

PurpleRequestFeature IMInvoker::_features;
PurpleRequestUiOps IMInvoker::_uiRequestOps = {
	_features,
	purpleRequestInput,
	purpleRequestChoice,
	purpleRequestAction,
	purpleRequestWait,
	purpleRequestWaitUpdate,
	purpleRequestFields,
	purpleRequestFile,
	purpleRequestFolder,
	purpleRequestClose,
	NULL,
	NULL,
	NULL,
	NULL
};

PurpleWhiteboardUiOps IMInvoker::_uiWhiteboardOps = {
	purpleCreateWB,
	purpleDestroyWB,
	purpleSetDimensions,
	purpleSetBrush,
	purpleDrawPont,
	purpleDrawLine,
	purpleClearWB,
	NULL,
	NULL,
	NULL,
	NULL
};
	
PurpleCoreUiOps IMInvoker::_uiCoreOps = {
	NULL,
	NULL,
	purpleUIInit,
	NULL,
	NULL,
	NULL,
	NULL,
	NULL
};

DelayedEventQueue* IMInvoker::_eventQueue = NULL;

tthread::mutex IMInvoker::_initMutex;
tthread::condition_variable IMInvoker::_initCond;

tthread::mutex IMInvoker::_accountMutex;
std::map<PurpleAccount*, IMInvoker*> IMInvoker::_accountInstances;

void IMInvoker::initLibPurple(void *userdata, const std::string event) {
	_initMutex.lock();

	_uiInfo = g_hash_table_new(g_str_hash, g_str_equal);
//	g_hash_table_insert(_uiInfo, "name", (char*)"uscxml");
//	g_hash_table_insert(_uiInfo, "version", "0.0.3");
//	g_hash_table_insert(_uiInfo, "website", "http://uscxml.tk.informatik.tu-darmstadt.de");
//	g_hash_table_insert(_uiInfo, "dev_website", "http://uscxml.tk.informatik.tu-darmstadt.de");
//	g_hash_table_insert(_uiInfo, "client_type", "pc");

	_gRand = g_rand_new();
	
	/* Set a custom user directory (optional) */
	//purple_util_set_user_dir(CUSTOM_USER_DIRECTORY);

	/* We do not want any debugging for now to keep the noise to a minimum. */
	purple_debug_set_enabled(false);
	
	purple_core_set_ui_ops(&_uiCoreOps);
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

	_initMutex.unlock();
	_initCond.notify_all();

}

void IMInvoker::buddyStatusChangedCB(PurpleBuddy *buddy, PurpleStatus *old, PurpleStatus *newstatus) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
	
	std::string buddyName = purple_buddy_get_name(buddy);
	inst->_dataModelVars.compound["buddies"].compound[buddyName] = buddyToData(buddy);
}

void IMInvoker::buddyIdleChangeCB(PurpleBuddy *buddy, gboolean old_idle, gboolean idle) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
}

void IMInvoker::buddyUpdateIdleCB() {
}

void IMInvoker::buddyAddedCB(PurpleBuddy* buddy) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
}

void IMInvoker::buddyRemovedCB(PurpleBuddy* buddy) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
}

void IMInvoker::buddyCapsChangedCB(PurpleBuddy* buddy, PurpleMediaCaps newcaps, PurpleMediaCaps oldcaps) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
}

gboolean IMInvoker::jabberRcvdPresenceCB(PurpleConnection *gc, const char *type, const char *from, xmlnode *presence) {
	PurpleAccount *account = purple_connection_get_account(gc);
	GET_INSTANCE_IN_CALLBACK(account);
}

void IMInvoker::buddySignOnOffCB(PurpleBuddy *buddy) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	tthread::lock_guard<tthread::mutex> lock(_accountMutex);
	if (_accountInstances.find(account) == _accountInstances.end()) {
		LOG(ERROR) << "Callback for unknown account called";
		return;
	}
	IMInvoker* inst = _accountInstances[account];
	
	std::string buddyName = purple_buddy_get_name(buddy);
	inst->_dataModelVars.compound["buddies"].compound[buddyName] = buddyToData(buddy);
}

void IMInvoker::signedOnCB(PurpleConnection *gc, gpointer null) {
	PurpleSavedStatus* status = purple_savedstatus_new(NULL, PURPLE_STATUS_AVAILABLE);
	purple_savedstatus_activate(status);	
}

	
Data IMInvoker::buddyToData(PurpleBuddy *buddy) {
	Data data;
	std::string buddyName = purple_buddy_get_name(buddy);
	
	if (purple_buddy_get_name(buddy))          data.compound["name"] = Data(purple_buddy_get_name(buddy), Data::VERBATIM);
	if (purple_buddy_get_alias(buddy))         data.compound["alias"] = Data(purple_buddy_get_alias(buddy), Data::VERBATIM);
	if (purple_buddy_get_alias_only(buddy))    data.compound["aliasOnly"] = Data(purple_buddy_get_alias_only(buddy), Data::VERBATIM);
	if (purple_buddy_get_server_alias(buddy))  data.compound["server"] = Data(purple_buddy_get_server_alias(buddy), Data::VERBATIM);
	
	PurpleGroup* group = purple_buddy_get_group(buddy);
	if (group) {
		if (purple_group_get_name(group))        data.compound["group"] = Data(purple_group_get_name(group), Data::VERBATIM);
	}

	PurpleBuddyIcon* icon = purple_buddy_get_icon(buddy);
	if (icon) {
		size_t iconSize = 0;
		gconstpointer iconData = purple_buddy_icon_get_data(icon, &iconSize);
		data.compound["icon"] = Data((char*)iconData, iconSize, false);
	}
	
	PurplePresence* presence = purple_buddy_get_presence(buddy);

	if (presence) {
		GList *statusElem;
		GList *statusList = purple_presence_get_statuses(presence);
		PurpleStatus* status;

		for(statusElem = statusList; statusElem; statusElem = statusElem->next) {
			status = (PurpleStatus*)statusElem->data;
			const char* statusId = purple_status_get_id(status);
			const char* statusName = purple_status_get_name(status);
			PurpleStatusPrimitive statusPrimitive = purple_primitive_get_type_from_id(statusId);
			
			// only include active states
			if(statusPrimitive == PURPLE_STATUS_UNSET || !purple_presence_is_status_primitive_active(presence, statusPrimitive))
				continue;
			
			if (statusName) data.compound["status"].compound[statusId] = Data(statusName, Data::VERBATIM);
			
			PurpleStatusType* statusType = purple_status_get_type(status);

			GList *statusAttrElem;
			GList *statusAttrList = purple_status_type_get_attrs(statusType);
			PurpleStatusAttr* statusAttr;
			for(statusAttrElem = statusAttrList; statusAttrElem; statusAttrElem = statusAttrElem->next) {
				statusAttr = (PurpleStatusAttr*)statusAttrElem->data;
				const char* statusAttrId = purple_status_attr_get_id(statusAttr);
				const char* statusAttrName = purple_status_attr_get_name(statusAttr);
				
				PurpleValue* statusAttrValue = purple_status_attr_get_value(statusAttr);
				if (statusAttrValue) {
					Data purpleValue = purpleValueToData(statusAttrValue);
					if (purpleValue) {
						data.compound["status"].compound[statusId].compound[statusAttrId].compound["value"] = purpleValue;
						if (statusAttrName) {
							data.compound["status"].compound[statusId].compound[statusAttrId].compound["name"] = Data(statusAttrName, Data::VERBATIM);
						}
					}
				}
			}
			
			data.compound["status"].compound[statusId].compound["active"] = Data((bool)purple_status_is_active(status));
			data.compound["status"].compound[statusId].compound["available"] = Data((bool)purple_status_is_available(status));
			data.compound["status"].compound[statusId].compound["exclusive"] = Data((bool)purple_status_is_exclusive(status));
			data.compound["status"].compound[statusId].compound["active"] = Data((bool)purple_status_is_active(status));
			data.compound["status"].compound[statusId].compound["independent"] = Data((bool)purple_status_is_independent(status));
			data.compound["status"].compound[statusId].compound["online"] = Data((bool)purple_status_is_online(status));
			
			
			PurpleValue* statusValue = purple_status_get_attr_value(status, statusId);
			if (statusValue)
				data.compound["status"].compound[statusId].compound["value"] = purpleValueToData(statusValue);
						
		}
		
	}
	std::cout << Data::toJSON(data);
	return data;
}

Data IMInvoker::purpleValueToData(PurpleValue* value) {
	Data data;
	switch (purple_value_get_type(value)) {
		case PURPLE_TYPE_BOOLEAN:
			if (purple_value_get_boolean(value))
				data = Data("true");
			data = Data("false");
			break;
		case PURPLE_TYPE_STRING:
			if (purple_value_get_string(value)) {
				data = Data(purple_value_get_string(value), Data::VERBATIM);
				std::cout << purple_value_get_string(value) << std::endl;
			}
			break;
		case PURPLE_TYPE_CHAR:
			Data(purple_value_get_char(value));
			break;
		case PURPLE_TYPE_UCHAR:
			Data(purple_value_get_uchar(value));
			break;
		case PURPLE_TYPE_SHORT:
			Data(purple_value_get_short(value));
			break;
		case PURPLE_TYPE_USHORT:
			Data(purple_value_get_ushort(value));
			break;
		case PURPLE_TYPE_INT:
			Data(purple_value_get_int(value));
			break;
		case PURPLE_TYPE_UINT:
			Data(purple_value_get_uint(value));
			break;
		case PURPLE_TYPE_LONG:
			Data(purple_value_get_long(value));
			break;
		case PURPLE_TYPE_ULONG:
			Data(purple_value_get_ulong(value));
			break;
		case PURPLE_TYPE_INT64:
			Data(purple_value_get_int64(value));
			break;
		case PURPLE_TYPE_UINT64:
			Data(purple_value_get_uint64(value));
			break;
		case PURPLE_TYPE_OBJECT:
		case PURPLE_TYPE_POINTER:
		case PURPLE_TYPE_ENUM:
		case PURPLE_TYPE_BOXED:
		case PURPLE_TYPE_UNKNOWN:
		case PURPLE_TYPE_SUBTYPE:
			LOG(ERROR) << "purple thingy not supported";
			break;
	}
	return data;
}
	
IMInvoker::IMInvoker() {
	_account = NULL;
	if (!_eventQueue) {
		tthread::lock_guard<tthread::mutex> lock(_initMutex);
		_eventQueue = new DelayedEventQueue();
		_eventQueue->addEvent("initLibPurple", IMInvoker::initLibPurple, 0, NULL);
		_eventQueue->start();
		// make sure to have the shebang initialized when we leave
		_initCond.wait(_initMutex);
	}

}

IMInvoker::~IMInvoker() {
	if (_account) {
		_accountMutex.lock();
		_accountInstances.erase(_account);
		purple_account_destroy(_account);
		_accountMutex.unlock();
	}
};

boost::shared_ptr<InvokerImpl> IMInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<IMInvoker> invoker = boost::shared_ptr<IMInvoker>(new IMInvoker());
	return invoker;
}

Data IMInvoker::getDataModelVariables() {
	tthread::lock_guard<tthread::mutex> lock(_accountMutex);
	return _dataModelVars;
}

void IMInvoker::send(const SendRequest& req) {
	EventContext* ctx = new EventContext();
	ctx->sendReq = req;
	ctx->instance = this;
	
	std::string eventId = UUID::getUUID();
	_eventQueue->addEvent(eventId, IMInvoker::send, 0, ctx);
	return;
}

void IMInvoker::send(void *userdata, const std::string event) {
	// we are in the thread that manages all of libpurple
	EventContext* ctx = (EventContext*)userdata;
#if 0
	if (boost::iequals(ctx->sendReq.name, "im.send")) {
		if (ctx->instance->_account) {
			std::string receiver;
			Event::getParam(ctx->sendReq.params, "receiver", receiver);

			Data data;
			Event::getParam(ctx->sendReq.params, "data", data);
			
			//			purple_conv_im_send
			PurpleConversation* conv = purple_conversation_new(PURPLE_CONV_TYPE_IM, ctx->instance->_account, receiver.c_str());
			purple_conv_im_send(purple_conversation_get_im_data(conv), ctx->sendReq.content.c_str());
			
#if 0
			if (data.binary) {
				PurpleConnection *gc = purple_account_get_connection(ctx->instance->_account);
				PurplePlugin *prpl;
				PurplePluginProtocolInfo *prpl_info;

				
				if (gc) {
					prpl = purple_connection_get_prpl(gc);
					prpl_info = PURPLE_PLUGIN_PROTOCOL_INFO(prpl);
					
//					if (prpl_info->send_file &&
//							(prpl_info->can_receive_file
//							 && prpl_info->can_receive_file(gc, receiver.c_str())))
//						prpl_info->send_file(gc, receiver.c_str(), file);
						prpl_info->send_raw(gc, data.binary->_data, data.binary->_size);
				}

			}
#endif
		}
	}
#endif
	delete(ctx);
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

void IMInvoker::invoke(void *userdata, const std::string event) {
	_accountMutex.lock();

	EventContext* ctx = (EventContext*)userdata;
	IMInvoker* instance = ctx->instance;
	
	std::string username;
	Event::getParam(ctx->invokeReq.params, "username", username);
	std::string protocolId;
	Event::getParam(ctx->invokeReq.params, "protocol", protocolId);
	std::string password;
	Event::getParam(ctx->invokeReq.params, "password", password);
	
	instance->_account = purple_account_new(username.c_str(), protocolId.c_str());
	_accountInstances[instance->_account] = instance;
	
	purple_account_set_password(instance->_account, password.c_str(), NULL, NULL);
	
	purple_account_set_enabled(instance->_account, "uscxml", true);
		
	int handle;
	purple_signal_connect(purple_connections_get_handle(), "signed-on", &handle, PURPLE_CALLBACK(signedOnCB), NULL);
	
	purple_signal_connect(purple_blist_get_handle(), "buddy-signed-on", &handle, PURPLE_CALLBACK(buddySignOnOffCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-signed-off", &handle, PURPLE_CALLBACK(buddySignOnOffCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-status-changed", &handle, PURPLE_CALLBACK(buddyStatusChangedCB), NULL);

	purple_signal_connect(purple_blist_get_handle(), "buddy-idle-changed", &handle, PURPLE_CALLBACK(buddyIdleChangeCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "update-idle", &handle, PURPLE_CALLBACK(buddyUpdateIdleCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-added", &handle, PURPLE_CALLBACK(buddyAddedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-removed", &handle, PURPLE_CALLBACK(buddyRemovedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-caps-changed", &handle, PURPLE_CALLBACK(buddyCapsChangedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "jabber-receiving-presence", &handle, PURPLE_CALLBACK(jabberRcvdPresenceCB), NULL);
	
	delete(ctx);
	_accountMutex.unlock();
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
	// unused
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

void IMInvoker::purpleUIInit(void) {
	purple_accounts_set_ui_ops(&_uiAccountOps);
	purple_xfers_set_ui_ops(&_uiXferOps);
//	purple_blist_set_ui_ops(&_uiBuddyOps);
//	purple_notify_set_ui_ops(&_uiNotifyOps);
//	purple_privacy_set_ui_ops(&_uiPrivacyOps);
//	purple_request_set_ui_ops(&_uiRequestOps);
//	purple_connections_set_ui_ops(&_uiConnectOps);
//	purple_whiteboard_set_ui_ops(&_uiWhiteboardOps);
	purple_conversations_set_ui_ops(&_uiConvOps);
}
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

//libpurple conversation operations
void IMInvoker::purpleCreateConversation(PurpleConversation *conv) {}
void IMInvoker::purpleDestroyConversation(PurpleConversation *conv) {}
void IMInvoker::purpleWriteChat(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime) {}
void IMInvoker::purpleWriteIm(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime) {}
void IMInvoker::purpleWriteConv(PurpleConversation *conv, const char *name, const char *alias, const char *message, PurpleMessageFlags flags, time_t mtime) {
	const char *who;
	if (alias && *alias)
		who = alias;
	else if (name && *name)
		who = name;
	else
		who = NULL;
	
	printf("(%s) %s %s: %s\n", purple_conversation_get_name(conv),
				 purple_utf8_strftime("(%H:%M:%S)", localtime(&mtime)),
				 who, message);
}
void IMInvoker::purpleChatAddUsers(PurpleConversation *conv, GList *cbuddies, gboolean new_arrivals) {}
void IMInvoker::purpleChatRenameUser(PurpleConversation *conv, const char *old_name, const char *new_name, const char *new_alias) {}
void IMInvoker::purpleChatRemoveUsers(PurpleConversation *conv, GList *users) {}
void IMInvoker::purpleChatUpdateUser(PurpleConversation *conv, const char *user) {}
void IMInvoker::purplePresentConversation(PurpleConversation *conv) {}
gboolean IMInvoker::purpleHasFocus(PurpleConversation *conv) {
	return true;
}
gboolean IMInvoker::purpleCustomSmileyAdd(PurpleConversation *conv, const char *smile, gboolean remote) {
	return true;
}
void IMInvoker::purpleCustomSmileyWrite(PurpleConversation *conv, const char *smile, const guchar *data, gsize size) {}
void IMInvoker::purpleCustomSmileyClose(PurpleConversation *conv, const char *smile) {}
void IMInvoker::purpleSendConfirm(PurpleConversation *conv, const char *message) {}

// buddy operations
void IMInvoker::purpleNewList(PurpleBuddyList *list) {
	std::cout << "purpleNewList" << std::endl;
}
void IMInvoker::purpleNewNode(PurpleBlistNode *node) {
	std::cout << "purpleNewNode" << std::endl;
}
void IMInvoker::purpleShow(PurpleBuddyList *list) {
	std::cout << "purpleShow" << std::endl;
}
void IMInvoker::purpleUpdate(PurpleBuddyList *list, PurpleBlistNode *node) {
}
void IMInvoker::purpleRemove(PurpleBuddyList *list, PurpleBlistNode *node) {}
void IMInvoker::purpleDestroy(PurpleBuddyList *list) {}
void IMInvoker::purpleSetVisible(PurpleBuddyList *list, gboolean show) {}
void IMInvoker::purpleRequestAddBuddy(PurpleAccount *account, const char *username, const char *group, const char *alias) {
	std::cout << "purpleRequestAddBuddy" << std::endl;
}
void IMInvoker::purpleRequestAddChat(PurpleAccount *account, PurpleGroup *group, const char *alias, const char *name) {
	std::cout << "purpleRequestAddChat" << std::endl;
}
void IMInvoker::purpleRequestAddGroup(void) {
	std::cout << "purpleRequestAddGroup" << std::endl;
}
void IMInvoker::purpleSaveNode(PurpleBlistNode *node) {}
void IMInvoker::purpleRemoveNode(PurpleBlistNode *node) {}
void IMInvoker::purpleSaveAccount(PurpleAccount *account) {}

// file transfer operations
void IMInvoker::purpleNewXfer(PurpleXfer *xfer) {
	std::cout << "purpleNewXfer" << std::endl;
}
void IMInvoker::purpleDestroy(PurpleXfer *xfer) {
	std::cout << "purpleDestroy" << std::endl;
}
void IMInvoker::purpleAddXfer(PurpleXfer *xfer) {
	std::cout << "purpleAddXfer" << std::endl;
}
void IMInvoker::purpleUpdateProgress(PurpleXfer *xfer, double percent) {
	std::cout << "purpleUpdateProgress" << std::endl;
}
void IMInvoker::purpleCancelLocal(PurpleXfer *xfer) {
	std::cout << "purpleCancelLocal" << std::endl;
}
void IMInvoker::purpleCancelRemote(PurpleXfer *xfer) {
	std::cout << "purpleCancelRemote" << std::endl;
}
gssize IMInvoker::purpleWrite(PurpleXfer *xfer, const guchar *buffer, gssize size) {
	std::cout << "purpleWrite" << std::endl;
}
gssize IMInvoker::purpleRead(PurpleXfer *xfer, guchar **buffer, gssize size) {
	std::cout << "purpleRead" << std::endl;
}
void IMInvoker::purpleDataNotSent(PurpleXfer *xfer, const guchar *buffer, gsize size) {
	std::cout << "purpleDataNotSent" << std::endl;
}
void IMInvoker::purpleAddThumbnail(PurpleXfer *xfer, const gchar *formats) {
	std::cout << "purpleAddThumbnail" << std::endl;
}

// notification operations
void* IMInvoker::purpeNotifyMessage(PurpleNotifyMsgType type, const char *title, const char *primary, const char *secondary, PurpleRequestCommonParameters *cpar) {
	return NULL;
}
void* IMInvoker::purpeNotifyEmail(PurpleConnection *gc, const char *subject, const char *from, const char *to, const char *url) {
	return NULL;
}
void* IMInvoker::purpeNotifyEmails(PurpleConnection *gc, size_t count, gboolean detailed, const char **subjects, const char **froms, const char **tos, const char **urls) {
	return NULL;
}
void* IMInvoker::purpeNotifyFormatted(const char *title, const char *primary, const char *secondary, const char *text) {
	return NULL;
}
void* IMInvoker::purpeNotifySearchResults(PurpleConnection *gc, const char *title, const char *primary, const char *secondary, PurpleNotifySearchResults *results, gpointer user_data) {
	return NULL;
}
void IMInvoker::purpeNotifySearchResultsNewRows(PurpleConnection *gc, PurpleNotifySearchResults *results, void *data) {}
void* IMInvoker::purpeNotifyUserInfo(PurpleConnection *gc, const char *who, PurpleNotifyUserInfo *user_info) {
	return NULL;
}
void* IMInvoker::purpeNotifyURI(const char *uri) {
	return NULL;
}
void IMInvoker::purpeNotifyClose(PurpleNotifyType type, void *ui_handle) {}

// privacy ui operations
void IMInvoker::purplePermitAdded(PurpleAccount *account, const char *name) {}
void IMInvoker::purplePermitRemoved(PurpleAccount *account, const char *name) {}
void IMInvoker::purpleDebyAdded(PurpleAccount *account, const char *name) {}
void IMInvoker::purpleDenyRemoved(PurpleAccount *account, const char *name) {}

	
// request ui operations
void* IMInvoker::purpleRequestInput(const char *title, const char *primary,
																		const char *secondary, const char *default_value,
																		gboolean multiline, gboolean masked, gchar *hint,
																		const char *ok_text, GCallback ok_cb,
																		const char *cancel_text, GCallback cancel_cb,
																		PurpleRequestCommonParameters *cpar, void *user_data) {}
void* IMInvoker::purpleRequestChoice(const char *title, const char *primary,
																		 const char *secondary, gpointer default_value,
																		 const char *ok_text, GCallback ok_cb, const char *cancel_text,
																		 GCallback cancel_cb, PurpleRequestCommonParameters *cpar,
																		 void *user_data, va_list choices) {}
void* IMInvoker::purpleRequestAction(const char *title, const char *primary,
																		 const char *secondary, int default_action,
																		 PurpleRequestCommonParameters *cpar, void *user_data,
																		 size_t action_count, va_list actions) {}
void* IMInvoker::purpleRequestWait(const char *title, const char *primary,
																	 const char *secondary, gboolean with_progress,
																	 PurpleRequestCancelCb cancel_cb,
																	 PurpleRequestCommonParameters *cpar, void *user_data) {}

void IMInvoker::purpleRequestWaitUpdate(void *ui_handle, gboolean pulse, gfloat fraction) {}
void* IMInvoker::purpleRequestFields(const char *title, const char *primary,
																		 const char *secondary, PurpleRequestFields *fields,
																		 const char *ok_text, GCallback ok_cb,
																		 const char *cancel_text, GCallback cancel_cb,
																		 PurpleRequestCommonParameters *cpar, void *user_data) {}
void* IMInvoker::purpleRequestFile(const char *title, const char *filename,
																	 gboolean savedialog, GCallback ok_cb, GCallback cancel_cb,
																	 PurpleRequestCommonParameters *cpar, void *user_data) {}
void* IMInvoker::purpleRequestFolder(const char *title, const char *dirname,
																		 GCallback ok_cb, GCallback cancel_cb,
																		 PurpleRequestCommonParameters *cpar, void *user_data) {}
void IMInvoker::purpleRequestClose(PurpleRequestType type, void *ui_handle) {}


// connection ui operations
void IMInvoker::purpleConnectProgress(PurpleConnection *gc, const char *text, size_t step, size_t step_count) {}
void IMInvoker::purpleConnected(PurpleConnection *gc) {}
void IMInvoker::purpleDisonnected(PurpleConnection *gc) {}
void IMInvoker::purpleNotice(PurpleConnection *gc, const char *text) {}
void IMInvoker::purpleNetworkConnected(void) {}
void IMInvoker::purpleNetworkDisconnected(void) {}
void IMInvoker::purpleReportDisconnect(PurpleConnection *gc, PurpleConnectionError reason, const char *text) {}

// whiteboard ui operations
void IMInvoker::purpleCreateWB(PurpleWhiteboard *wb) {}
void IMInvoker::purpleDestroyWB(PurpleWhiteboard *wb) {}
void IMInvoker::purpleSetDimensions(PurpleWhiteboard *wb, int width, int height) {}
void IMInvoker::purpleSetBrush(PurpleWhiteboard *wb, int size, int color) {}
void IMInvoker::purpleDrawPont(PurpleWhiteboard *wb, int x, int y, int color, int size) {}
void IMInvoker::purpleDrawLine(PurpleWhiteboard *wb, int x1, int y1, int x2, int y2, int color, int size) {}
void IMInvoker::purpleClearWB(PurpleWhiteboard *wb) {}

}