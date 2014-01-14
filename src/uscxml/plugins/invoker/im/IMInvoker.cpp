/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "IMInvoker.h"
#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"
#include <boost/algorithm/string.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define GET_INSTANCE_IN_CALLBACK(account) \
tthread::lock_guard<tthread::recursive_mutex> lock(_accountMutex); \
IMInvoker* inst = NULL;\
if (_accountInstances.find(account) == _accountInstances.end()) { \
	LOG(ERROR) << "Callback for unknown account called"; \
} else {\
	inst = _accountInstances[account];\
}


namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new IMInvokerProvider() );
	return true;
}
#endif

Data IMInvoker::_pluginData;
GHashTable* IMInvoker::_uiInfo = NULL;
GRand* IMInvoker::_gRand = NULL;

PurpleEventLoopUiOps IMInvoker::_uiEventLoopOps = {
	purpleEventTimeoutAdd,
	purpleEventTimeoutRemove,
	purpleEventInputAdd,
	purpleEventInputRemove,
	purpleEventInputGetError,
	purpleEventTimeoutAddSec,
	NULL,
	NULL,
	NULL
};

PurpleDebugUiOps IMInvoker::_uiDebugOps = {
	purpleDebugPrint,
	purpleDebugIsEnabled,
	NULL, NULL, NULL, NULL
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
PurpleConversationUiOps IMInvoker::_uiConvOps = {
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

#if 0
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
#endif

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
	purplePrefsInit,
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

tthread::recursive_mutex IMInvoker::_accountMutex;
std::map<PurpleAccount*, IMInvoker*> IMInvoker::_accountInstances;

void IMInvoker::setupPurpleSignals() {
	int handle;
	// connection signals
	purple_signal_connect(purple_connections_get_handle(), "signed-on", &handle, PURPLE_CALLBACK(signedOnCB), NULL);

	// conversation signals
	purple_signal_connect(purple_conversations_get_handle(), "conversation-created", &handle, PURPLE_CALLBACK(conversationCreatedCB), NULL);
	purple_signal_connect(purple_conversations_get_handle(), "chat-joined", &handle, PURPLE_CALLBACK(chatJoinedCB), NULL);
	purple_signal_connect(purple_conversations_get_handle(), "chat-join-failed", &handle, PURPLE_CALLBACK(chatJoinFailedCB), NULL);
	purple_signal_connect(purple_conversations_get_handle(), "buddy-typing", &handle, PURPLE_CALLBACK(buddyTypingCB), NULL);
	purple_signal_connect(purple_conversations_get_handle(), "buddy-typed", &handle, PURPLE_CALLBACK(buddyTypedCB), NULL);
	purple_signal_connect(purple_conversations_get_handle(), "buddy-typing-stopped", &handle, PURPLE_CALLBACK(buddyTypingStoppedCB), NULL);

	// buddy signals
	purple_signal_connect(purple_blist_get_handle(), "buddy-signed-on", &handle, PURPLE_CALLBACK(buddyEventCB), GINT_TO_POINTER(PURPLE_BUDDY_SIGNON));
	purple_signal_connect(purple_blist_get_handle(), "buddy-signed-off", &handle, PURPLE_CALLBACK(buddyEventCB), GINT_TO_POINTER(PURPLE_BUDDY_SIGNOFF));
	purple_signal_connect(purple_blist_get_handle(), "buddy-got-login-time", &handle, PURPLE_CALLBACK(buddyEventCB), GINT_TO_POINTER(PURPLE_BUDDY_SIGNON_TIME));
	purple_signal_connect(purple_blist_get_handle(), "buddy-idle-changed", &handle, PURPLE_CALLBACK(buddyIdleChangedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-status-changed", &handle, PURPLE_CALLBACK(buddyStatusChangedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-icon-changed", &handle, PURPLE_CALLBACK(buddyEventCB), GINT_TO_POINTER(PURPLE_BUDDY_ICON));
	purple_signal_connect(purple_blist_get_handle(), "buddy-added", &handle, PURPLE_CALLBACK(buddyAddedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-removed", &handle, PURPLE_CALLBACK(buddyRemovedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "blist-node-aliased", &handle, PURPLE_CALLBACK(blistNodeAliasedCB), NULL);
	purple_signal_connect(purple_blist_get_handle(), "buddy-caps-changed", &handle, PURPLE_CALLBACK(buddyCapsChangedCB), NULL);

	// xfer signals
	purple_signal_connect(purple_xfers_get_handle(), "file-recv-request", &handle, PURPLE_CALLBACK(fileRecvRequestCB), NULL);

}

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

		if (plugin->info->type == PURPLE_PLUGIN_PROTOCOL) {
			_pluginData.compound["protocol"].compound[plugin->info->id] = pluginData;
		} else if (plugin->info->type == PURPLE_PLUGIN_STANDARD) {
//			_pluginData.compound["standard"].compound[plugin->info->id] = pluginData;
		} else if (plugin->info->type == PURPLE_PLUGIN_LOADER) {
//			_pluginData.compound["loader"].compound[plugin->info->id] = pluginData;
		}
	}

	_initMutex.unlock();
	_initCond.notify_all();
}

// purple event callbacks
void IMInvoker::signedOnCB(PurpleConnection *gc, gpointer null) {
	PurpleAccount *account = purple_connection_get_account(gc);
	GET_INSTANCE_IN_CALLBACK(account);
	if (!inst)
		return;

#if 0
	GSList *buddies = purple_find_buddies(purple_connection_get_account(gc), NULL);
	GSList *cur;
	for (cur = buddies; cur; cur = cur->next) {
		buddyAddedCB((PurpleBuddy *)cur->data);
	}
	g_slist_free(buddies);
#endif

	// set my status to active
	PurpleSavedStatus* status = purple_savedstatus_new(NULL, PURPLE_STATUS_AVAILABLE);
	purple_savedstatus_activate(status);

	Event retEv("im.signed.on");
	inst->returnEvent(retEv);
}

void IMInvoker::conversationCreatedCB(PurpleConversation *conv, void *data) {}
void IMInvoker::chatJoinedCB(PurpleConversation *conv, void *data) {}
void IMInvoker::chatJoinFailedCB(PurpleConnection *gc, GHashTable *components) {}
void IMInvoker::buddyTypingCB(PurpleAccount *account, const char *name, void *data) {
	std::cout << "buddyTypingCB" << std::endl;
}
void IMInvoker::buddyTypedCB(PurpleAccount *account, const char *name, void *data) {
	std::cout << "buddyTypedCB" << std::endl;
}
void IMInvoker::buddyTypingStoppedCB(PurpleAccount *account, const char *name, void *data) {
	std::cout << "buddyTypingStoppedCB" << std::endl;
}

void IMInvoker::buddyEventCB(PurpleBuddy *buddy, PurpleBuddyEvent event) {
	if (!buddy)
		return;

	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
	if (!inst)
		return;

	switch (event) {
	case PURPLE_BUDDY_SIGNOFF:
	case PURPLE_BUDDY_SIGNON: {
		PurplePresence* presence = purple_buddy_get_presence(buddy);
		PurpleStatus* status = purple_presence_get_active_status(presence);
		buddyStatusChangedCB(buddy, NULL, status, event);
		break;
	}
	case PURPLE_BUDDY_ICON:
		break;

	default:
		break;
	}

}

void IMInvoker::buddyIdleChangedCB(PurpleBuddy *buddy, gboolean old_idle, gboolean idle, PurpleBuddyEvent event) {
}

void IMInvoker::buddyStatusChangedCB(PurpleBuddy *buddy, PurpleStatus *old, PurpleStatus *newstatus, PurpleBuddyEvent event) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);

	std::string buddyName = purple_buddy_get_name(buddy);
	Data buddyData = buddyToData(buddy);
	inst->_dataModelVars.compound["buddies"].compound[buddyName] = buddyData;

	Event retEv("im.buddy.status.changed");
	retEv.data = buddyData;
	inst->returnEvent(retEv);

}

void IMInvoker::buddyAddedCB(PurpleBuddy* buddy) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
	if (!inst)
		return;

	std::string buddyName = purple_buddy_get_name(buddy);

	Event retEv("im.buddy.added");
	retEv.data.compound["name"] = Data(buddyName, Data::VERBATIM);
	inst->returnEvent(retEv);

	buddyStatusChangedCB(buddy, NULL, purple_presence_get_active_status(purple_buddy_get_presence(buddy)), PURPLE_BUDDY_NONE);

}

void IMInvoker::buddyRemovedCB(PurpleBuddy* buddy) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
	std::string buddyName = purple_buddy_get_name(buddy);

	Event retEv("im.buddy.removed");
	retEv.data.compound["name"] = Data(buddyName, Data::VERBATIM);
	inst->returnEvent(retEv);

	inst->_dataModelVars.compound["buddies"].compound.erase(buddyName);

}

void IMInvoker::blistNodeAliasedCB(PurpleBlistNode *node, char *old_alias) {
}

void IMInvoker::fileRecvRequestCB(PurpleXfer *xfer) {
	purple_xfer_set_local_filename(xfer, "");
}


void IMInvoker::buddyCapsChangedCB(PurpleBuddy* buddy, PurpleMediaCaps newcaps, PurpleMediaCaps oldcaps) {
	PurpleAccount *account = purple_buddy_get_account(buddy);
	GET_INSTANCE_IN_CALLBACK(account);
}

Data IMInvoker::statusToData(PurpleStatus *status) {
	Data data;
	const char* statusName = purple_status_get_name(status);
	if (statusName) data.compound["name"] = Data(statusName, Data::VERBATIM);

	PurpleStatusType* statusType = purple_status_get_status_type(status);

	GList *statusAttrElem;
	PurpleStatusAttribute* statusAttr;
	GList *statusAttrList = purple_status_type_get_attrs(statusType);

	for(statusAttrElem = statusAttrList; statusAttrElem; statusAttrElem = statusAttrElem->next) {
		statusAttr = (PurpleStatusAttribute*)statusAttrElem->data;
		const char* statusAttrId = purple_status_attribute_get_id(statusAttr);
		GValue* statusValue = purple_status_get_attr_value(status, statusAttrId);
		if (statusValue) {
			data.compound[statusAttrId] = purpleValueToData(statusValue);
		}
	}

	data.compound["active"] = Data((bool)purple_status_is_active(status));
	data.compound["available"] = Data((bool)purple_status_is_available(status));
	data.compound["exclusive"] = Data((bool)purple_status_is_exclusive(status));
	data.compound["active"] = Data((bool)purple_status_is_active(status));
	data.compound["independent"] = Data((bool)purple_status_is_independent(status));
	data.compound["online"] = Data((bool)purple_status_is_online(status));

	return data;
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
		data.compound["icon"] = Data((char*)iconData, iconSize, "application/octet-stream", false);
	}

	PurplePresence* presence = purple_buddy_get_presence(buddy);

	if (presence) {
		GList *statusElem;
		GList *statusList = purple_presence_get_statuses(presence);
		PurpleStatus* status;

		for(statusElem = statusList; statusElem; statusElem = statusElem->next) {
			status = (PurpleStatus*)statusElem->data;
			const char* statusId = purple_status_get_id(status);
			PurpleStatusPrimitive statusPrimitive = purple_primitive_get_type_from_id(statusId);

			// only include active states
			if(statusPrimitive == PURPLE_STATUS_UNSET || !purple_presence_is_status_primitive_active(presence, statusPrimitive))
				continue;
			data.compound["status"].compound[statusId] = statusToData(status);
		}

	}

	return data;
}

Data IMInvoker::purpleValueToData(GValue* value) {
	Data data;

	if (false) {
	} else if (g_type_check_value_holds(value, G_TYPE_CHAR)) {
		data = Data(g_value_get_schar(value), Data::VERBATIM);

	} else if (g_type_check_value_holds(value, G_TYPE_UCHAR)) {
		data = Data(g_value_get_uchar(value), Data::VERBATIM);

	} else if (g_type_check_value_holds(value, G_TYPE_BOOLEAN)) {
		data = Data(g_value_get_boolean(value));

	} else if (g_type_check_value_holds(value, G_TYPE_INT)) {
		data = Data(g_value_get_int(value));

	} else if (g_type_check_value_holds(value, G_TYPE_UINT)) {
		data = Data(g_value_get_uint(value));

	} else if (g_type_check_value_holds(value, G_TYPE_LONG)) {
		data = Data(g_value_get_long(value));

	} else if (g_type_check_value_holds(value, G_TYPE_ULONG)) {
		data = Data(g_value_get_ulong(value));

	} else if (g_type_check_value_holds(value, G_TYPE_INT64)) {
		data = Data(g_value_get_int64(value));

	} else if (g_type_check_value_holds(value, G_TYPE_FLOAT)) {
		data = Data(g_value_get_float(value));

	} else if (g_type_check_value_holds(value, G_TYPE_DOUBLE)) {
		data = Data(g_value_get_double(value));

	} else if (g_type_check_value_holds(value, G_TYPE_STRING)) {
		const gchar* tmp = g_value_get_string(value);
		if (tmp == NULL) {
			data = Data("", Data::VERBATIM);
		} else {
			data = Data(g_value_get_string(value), Data::VERBATIM);
		}

	} else if (g_type_check_value_holds(value, G_TYPE_OBJECT) ||
	           g_type_check_value_holds(value, G_TYPE_PARAM) ||
	           g_type_check_value_holds(value, G_TYPE_POINTER) ||
	           g_type_check_value_holds(value, G_TYPE_FLAGS) ||
	           g_type_check_value_holds(value, G_TYPE_ENUM)) {
		LOG(ERROR) << "purple thingy not supported";
	} else {
		LOG(ERROR) << "purple thingy unknown";
	}
	return data;
}

IMInvoker::IMInvoker() {
	_account = NULL;
}

IMInvoker::~IMInvoker() {
	if (_account) {
		_accountMutex.lock();
		_accountInstances.erase(_account);
//		purple_account_destroy(_account);
		_accountMutex.unlock();
	}
};

boost::shared_ptr<InvokerImpl> IMInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<IMInvoker> invoker = boost::shared_ptr<IMInvoker>(new IMInvoker());

	if (!_eventQueue) {
		tthread::lock_guard<tthread::mutex> lock(_initMutex);
		_eventQueue = new DelayedEventQueue();
		_eventQueue->addEvent("initLibPurple", IMInvoker::initLibPurple, 0, NULL);
		_eventQueue->start();
		// make sure to have the shebang initialized when we leave
		_initCond.wait(_initMutex);
	}

	invoker->_dataModelVars.compound["plugins"] = _pluginData;
	return invoker;
}

Data IMInvoker::getDataModelVariables() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_accountMutex);
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

	if (!ctx)
		return;

	if (!ctx->instance || !ctx->instance->_account) {
		ctx->instance->returnErrorExecution("No account available");
		delete(ctx);
		return;
	}

	if (iequals(ctx->sendReq.name, "im.send")) {
		std::string receiver;
		Event::getParam(ctx->sendReq.params, "receiver", receiver);

		Data data;
		Event::getParam(ctx->sendReq.params, "data", data);

		PurpleIMConversation* conv = purple_im_conversation_new(ctx->instance->_account, receiver.c_str());
		if (ctx->sendReq.content.length() > 0)
			purple_conversation_send(PURPLE_CONVERSATION(conv), ctx->sendReq.content.c_str());

#if 0
		if (data.binary) {
			PurpleConnection *gc = purple_account_get_connection(ctx->instance->_account);
			PurplePlugin *prpl;
			PurplePluginProtocolInfo *prpl_info;


			if (gc) {
				prpl = purple_connection_get_prpl(gc);
				prpl_info = PURPLE_PLUGIN_PROTOCOL_INFO(prpl);

//					if (prpl_info && prpl_info->new_xfer) {
//						PurpleXfer* xfer = (prpl_info->new_xfer)(purple_account_get_connection(ctx->instance->_account), receiver.c_str());
//						purple_xfer_set_local_filename(xfer, "/Users/sradomski/Documents/W3C Standards.pdf");
//						purple_xfer_set_filename(xfer, "asdfadsf.pdf");
//						purple_xfer_request(xfer);
//						purple_xfer_request_accepted(xfer, "/Users/sradomski/Documents/W3C Standards.pdf");
//					}

				//Set the filename
//					purple_xfer_set_local_filename(xfer, [[fileTransfer localFilename] UTF8String]);
//					purple_xfer_set_filename(xfer, [[[fileTransfer localFilename] lastPathComponent] UTF8String]);
//					xfer->ui_data
//					purple_xfer_request(xfer);

				serv_send_file(gc, "sradomski@localhost", "/Users/sradomski/Documents/W3C Standards.pdf");
//					if (prpl_info->send_file && (prpl_info->can_receive_file && prpl_info->can_receive_file(gc, receiver.c_str()))) {
//						prpl_info->send_file(gc, receiver.c_str(), "/Users/sradomski/Documents/W3C Standards.pdf");
//					}
//						prpl_info->send_raw(gc, data.binary->data, data.binary->size);
			}

		}
#endif
	} else if (iequals(ctx->sendReq.name, "im.buddy.add")) {
		std::string buddyName;
		Event::getParam(ctx->sendReq.params, "name", buddyName);

		std::string reqMsg;
		Event::getParam(ctx->sendReq.params, "msg", reqMsg);

		PurpleBuddy* buddy = purple_buddy_new(ctx->instance->_account, buddyName.c_str(), NULL);
		purple_blist_add_buddy(buddy, NULL, NULL, NULL);
		purple_account_add_buddy(ctx->instance->_account, buddy, reqMsg.c_str());

	} else if (iequals(ctx->sendReq.name, "im.buddy.remove")) {
		std::string buddyName;
		Event::getParam(ctx->sendReq.params, "name", buddyName);

		PurpleBuddy* buddy = purple_blist_find_buddy(ctx->instance->_account, buddyName.c_str());
		if (PURPLE_IS_BUDDY(buddy)) {
			purple_account_remove_buddy(ctx->instance->_account, buddy, purple_buddy_get_group(buddy));
			purple_blist_remove_buddy(buddy);
		}
	}

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

	GSList* buddies = purple_blist_get_buddies();
	GSList *cur;
	for (cur = buddies; cur; cur = cur->next) {
		std::string buddyName = purple_buddy_get_name((PurpleBuddy *)cur->data);
		Data buddyData = buddyToData((PurpleBuddy *)cur->data);
		instance->_dataModelVars.compound["buddies"].compound[buddyName] = buddyData;
	}
	g_slist_free(buddies);



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
		opMask |= DelayedEventQueue::DEQ_READ;
	if (cond & PURPLE_INPUT_WRITE)
		opMask |= DelayedEventQueue::DEQ_WRITE;

	guint eventId = g_rand_int(_gRand);
//	std::cout << "-- Input add " << eventId << " --------" << fd << std::endl;
	_eventQueue->addEvent(toStr(eventId), fd, opMask, purpleCallback, ctx, true);
	return eventId;
}

gboolean IMInvoker::purpleEventInputRemove(guint handle) {
//	std::cout << "-- Input del " << handle << std::endl;
	_eventQueue->cancelEvent(toStr(handle));
	return true;
}

int IMInvoker::purpleEventInputGetError(int fd, int *error) {
	int		  ret;
	socklen_t len;
	len = sizeof(*error);

	ret = getsockopt(fd, SOL_SOCKET, SO_ERROR, error, &len);
	if (!ret && !(*error)) {
		/*
		 * Taken from Fire's FaimP2PConnection.m:
		 * The job of this function is to detect if the connection failed or not
		 * There has to be a better way to do this
		 *
		 * Any socket that fails to connect will select for reading and writing
		 * and all reads and writes will fail
		 * Any listening socket will select for reading, and any read will fail
		 * So, select for writing, if you can write, and the write fails, not connected
		 */

		{
			fd_set thisfd;
			struct timeval timeout;

			FD_ZERO(&thisfd);
			FD_SET(fd, &thisfd);
			timeout.tv_sec = 0;
			timeout.tv_usec = 0;
			select(fd+1, NULL, &thisfd, NULL, &timeout);
			if(FD_ISSET(fd, &thisfd)) {
				ssize_t length = 0;
				char buffer[4] = {0, 0, 0, 0};

				length = write(fd, buffer, length);
				if(length == -1) {
					/* Not connected */
					ret = -1;
					*error = ENOTCONN;
				}
			}
		}
	}

	return ret;
}

void IMInvoker::purpleCallback(void *userdata, const std::string event) {
	PurpleEventContext* ctx = (PurpleEventContext*)userdata;
	if (ctx->function) {
		ctx->function(ctx->data);
		delete ctx;
	} else if(ctx->input) {
//		std::cout << "operating on " << ctx->inputFD << std::endl;
		ctx->input(ctx->data, ctx->inputFD, ctx->cond);
	}
}

void IMInvoker::purplePrefsInit(void) {
	purple_prefs_add_bool("/auto-login", false);
}

void IMInvoker::purpleDebugInit(void) {}

void IMInvoker::purpleUIInit(void) {
	purple_accounts_set_ui_ops(&_uiAccountOps);
//	purple_xfers_set_ui_ops(&_uiXferOps);
//	purple_blist_set_ui_ops(&_uiBuddyOps);
//	purple_notify_set_ui_ops(&_uiNotifyOps);
//	purple_privacy_set_ui_ops(&_uiPrivacyOps);
//	purple_request_set_ui_ops(&_uiRequestOps);
//	purple_connections_set_ui_ops(&_uiConnectOps);
//	purple_whiteboard_set_ui_ops(&_uiWhiteboardOps);
	purple_conversations_set_ui_ops(&_uiConvOps);
	purple_debug_set_ui_ops(&_uiDebugOps);

	setupPurpleSignals();

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
	// always accept all "may I add you as a buddy?" requests
	authorize_cb(message, user_data);
	return user_data;
}

void IMInvoker::accountCloseRequest(void *ui_handle) {
	std::cout << "accountCloseRequest" << std::endl;
}

//libpurple conversation operations
void IMInvoker::purpleCreateConversation(PurpleConversation *conv) {}
void IMInvoker::purpleDestroyConversation(PurpleConversation *conv) {}
void IMInvoker::purpleWriteChat(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime) {
	std::cout << "purpleWriteChat" << std::endl;
}
void IMInvoker::purpleWriteIm(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime) {
	std::cout << "purpleWriteIm" << std::endl;
}
void IMInvoker::purpleWriteConv(PurpleConversation *conv, const char *name, const char *alias, const char *message, PurpleMessageFlags flags, time_t mtime) {

	GET_INSTANCE_IN_CALLBACK(purple_conversation_get_account(conv));
	if (inst == NULL)
		return;

	Event msgRcvdEv;
	if (flags & PURPLE_MESSAGE_SEND)
		msgRcvdEv.name = "im.send.conv";
	if (flags & PURPLE_MESSAGE_RECV)
		msgRcvdEv.name = "im.rcvd.conv";

	if (alias && *alias)
		msgRcvdEv.data.compound["alias"] = Data(alias, Data::VERBATIM);
	if (name && *name)
		msgRcvdEv.data.compound["name"] = Data(name, Data::VERBATIM);

	msgRcvdEv.data.compound["conversation"] = Data(purple_conversation_get_name(conv), Data::VERBATIM);
	msgRcvdEv.data.compound["timestamp"] = Data(mtime);
	msgRcvdEv.data.compound["time"] = Data(purple_utf8_strftime("%T", localtime(&mtime)), Data::VERBATIM);
	msgRcvdEv.data.compound["date"] = Data(purple_utf8_strftime("%F", localtime(&mtime)), Data::VERBATIM);
	msgRcvdEv.data.compound["datetime"] = Data(purple_utf8_strftime("%c", localtime(&mtime)), Data::VERBATIM);

	msgRcvdEv.data.compound["raw"] = Data(message, Data::VERBATIM);
	if (flags & PURPLE_MESSAGE_RAW) {
		msgRcvdEv.data.compound["message"] = Data(message, Data::VERBATIM);
	} else {
		bool successParse = false; // unfortunate code layout as parsers operator= is private :(
		std::string origErrors;

		// try to parse as XHTML
		{
			NameSpacingParser parser = NameSpacingParser::fromXML(message);
			if (!parser.errorsReported()) {
				msgRcvdEv.data.compound["message"].node = parser.getDocument().getDocumentElement();
				successParse = true;
			} else {
				origErrors = parser.errors();
			}
		}

		// try again with added XHTML tags
		if (!successParse) {
			NameSpacingParser parser = NameSpacingParser::fromXML(std::string("<html xmlns='http://jabber.org/protocol/xhtml-im'>") +
			                           std::string("<body xmlns='http://www.w3.org/1999/xhtml'>") +
			                           message +
			                           std::string("</body>") +
			                           std::string("</html>"));
			if (!parser.errorsReported()) {
				msgRcvdEv.data.compound["message"].node = parser.getDocument().getDocumentElement();
				successParse = true;
			} else {
				LOG(ERROR) << "Cannot parse message as XHTML: " << origErrors << std::endl << message;
			}
		}

		if (successParse) {
			// prepare stripped message content
			std::list<Arabica::DOM::Node<std::string> > texts = DOMUtils::getElementsByType(msgRcvdEv.data.compound["message"].node, Arabica::DOM::Node_base::TEXT_NODE);
			std::stringstream ssTexts;
			std::string seperator;
			while(texts.size() > 0) {
				ssTexts << seperator << texts.front().getNodeValue();
				texts.pop_front();
				if (ssTexts.str().length() > 0 && isspace(ssTexts.str()[ssTexts.str().length() - 1])) {
					seperator = "";
				} else {
					seperator = " ";
				}
			}

			msgRcvdEv.data.compound["stripped"] = Data(ssTexts.str(), Data::VERBATIM);
		}
		// erase for now as JS dump croaks on dom nodes with cycles
		msgRcvdEv.data.compound.erase("message");
	}

	msgRcvdEv.data.compound["flags"].compound["send"]         = Data((bool)(flags & PURPLE_MESSAGE_SEND));
	msgRcvdEv.data.compound["flags"].compound["rcvd"]         = Data((bool)(flags & PURPLE_MESSAGE_RECV));
	msgRcvdEv.data.compound["flags"].compound["system"]       = Data((bool)(flags & PURPLE_MESSAGE_SYSTEM));
	msgRcvdEv.data.compound["flags"].compound["auoresponse"]  = Data((bool)(flags & PURPLE_MESSAGE_AUTO_RESP));
	msgRcvdEv.data.compound["flags"].compound["activeonly"]   = Data((bool)(flags & PURPLE_MESSAGE_ACTIVE_ONLY));
	msgRcvdEv.data.compound["flags"].compound["containsnick"] = Data((bool)(flags & PURPLE_MESSAGE_NICK));
	msgRcvdEv.data.compound["flags"].compound["nolog"]        = Data((bool)(flags & PURPLE_MESSAGE_NO_LOG));
	msgRcvdEv.data.compound["flags"].compound["whisper"]      = Data((bool)(flags & PURPLE_MESSAGE_WHISPER));
	msgRcvdEv.data.compound["flags"].compound["error"]        = Data((bool)(flags & PURPLE_MESSAGE_ERROR));
	msgRcvdEv.data.compound["flags"].compound["delayed"]      = Data((bool)(flags & PURPLE_MESSAGE_DELAYED));
	msgRcvdEv.data.compound["flags"].compound["raw"]          = Data((bool)(flags & PURPLE_MESSAGE_RAW));
	msgRcvdEv.data.compound["flags"].compound["images"]       = Data((bool)(flags & PURPLE_MESSAGE_IMAGES));
	msgRcvdEv.data.compound["flags"].compound["notify"]       = Data((bool)(flags & PURPLE_MESSAGE_NOTIFY));
	msgRcvdEv.data.compound["flags"].compound["nolinkify"]    = Data((bool)(flags & PURPLE_MESSAGE_NO_LINKIFY));
	msgRcvdEv.data.compound["flags"].compound["invisible"]    = Data((bool)(flags & PURPLE_MESSAGE_INVISIBLE));

	inst->returnEvent(msgRcvdEv);
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
	return 0;
}
gssize IMInvoker::purpleRead(PurpleXfer *xfer, guchar **buffer, gssize size) {
	std::cout << "purpleRead" << std::endl;
	return 0;
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
                                    PurpleRequestCommonParameters *cpar, void *user_data) {
	return NULL;
}
void* IMInvoker::purpleRequestChoice(const char *title, const char *primary,
                                     const char *secondary, gpointer default_value,
                                     const char *ok_text, GCallback ok_cb, const char *cancel_text,
                                     GCallback cancel_cb, PurpleRequestCommonParameters *cpar,
                                     void *user_data, va_list choices) {
	return NULL;
}
void* IMInvoker::purpleRequestAction(const char *title, const char *primary,
                                     const char *secondary, int default_action,
                                     PurpleRequestCommonParameters *cpar, void *user_data,
                                     size_t action_count, va_list actions) {
	return NULL;
}
void* IMInvoker::purpleRequestWait(const char *title, const char *primary,
                                   const char *secondary, gboolean with_progress,
                                   PurpleRequestCancelCb cancel_cb,
                                   PurpleRequestCommonParameters *cpar, void *user_data) {
	return NULL;
}

void IMInvoker::purpleRequestWaitUpdate(void *ui_handle, gboolean pulse, gfloat fraction) {

}
void* IMInvoker::purpleRequestFields(const char *title, const char *primary,
                                     const char *secondary, PurpleRequestFields *fields,
                                     const char *ok_text, GCallback ok_cb,
                                     const char *cancel_text, GCallback cancel_cb,
                                     PurpleRequestCommonParameters *cpar, void *user_data) {
	return NULL;
}
void* IMInvoker::purpleRequestFile(const char *title, const char *filename,
                                   gboolean savedialog, GCallback ok_cb, GCallback cancel_cb,
                                   PurpleRequestCommonParameters *cpar, void *user_data) {
	// click ok
	PurpleXfer *xfer = (PurpleXfer *)user_data;
	PurpleXferType xferType = purple_xfer_get_xfer_type(xfer);
	if (xferType == PURPLE_XFER_TYPE_RECEIVE) {
		((PurpleRequestFileCb)ok_cb)(user_data, filename);
	} else if (xferType == PURPLE_XFER_TYPE_SEND) {
		if (purple_xfer_get_local_filename(xfer) != NULL && purple_xfer_get_filename(xfer) != NULL) {
			((PurpleRequestFileCb)ok_cb)(user_data, purple_xfer_get_local_filename(xfer));
		} else {
			((PurpleRequestFileCb)cancel_cb)(user_data, purple_xfer_get_local_filename(xfer));
		}
	}
	return NULL;
}

void* IMInvoker::purpleRequestFolder(const char *title, const char *dirname,
                                     GCallback ok_cb, GCallback cancel_cb,
                                     PurpleRequestCommonParameters *cpar, void *user_data) {
	return NULL;
}

void IMInvoker::purpleRequestClose(PurpleRequestType type, void *ui_handle) {

}


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

// debug ui operations
void IMInvoker::purpleDebugPrint(PurpleDebugLevel level, const char *category, const char *arg_s) {
//	std::cout << category << ": " << arg_s << std::endl;
}

gboolean IMInvoker::purpleDebugIsEnabled(PurpleDebugLevel level, const char *category) {
	return true;
}


}