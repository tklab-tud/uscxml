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

#ifndef IMINVOKER_H_FNWG0XCQ
#define IMINVOKER_H_FNWG0XCQ

#include <uscxml/Interpreter.h>

extern "C" {
#include <libpurple/purple.h>
}

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

typedef enum {
    PURPLE_BUDDY_NONE                    = 0x00, /**< No events.                    */
    PURPLE_BUDDY_SIGNON                  = 0x01, /**< The buddy signed on.          */
    PURPLE_BUDDY_SIGNOFF                 = 0x02, /**< The buddy signed off.         */
    PURPLE_BUDDY_INFO_UPDATED            = 0x10, /**< The buddy's information (profile) changed.     */
    PURPLE_BUDDY_ICON                    = 0x40, /**< The buddy's icon changed.     */
    PURPLE_BUDDY_MISCELLANEOUS           = 0x80, /**< The buddy's service-specific miscalleneous info changed.     */
    PURPLE_BUDDY_SIGNON_TIME             = 0x11, /**< The buddy's signon time changed.     */
    PURPLE_BUDDY_EVIL                    = 0x12,  /**< The buddy's warning level changed.     */
    PURPLE_BUDDY_DIRECTIM_CONNECTED      = 0x14, /**< Connected to the buddy via DirectIM.  */
    PURPLE_BUDDY_DIRECTIM_DISCONNECTED   = 0x18, /**< Disconnected from the buddy via DirectIM.  */
    PURPLE_BUDDY_NAME                    = 0x20 /**<Buddy name (UID) changed. */
} PurpleBuddyEvent;

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

private:
	static bool _libPurpleIsInitialized;
	static Data _pluginData;

	Data _dataModelVars;

	static Data buddyToData(PurpleBuddy *buddy);
	static Data statusToData(PurpleStatus *status);
	static Data purpleValueToData(PurpleValue* value);

	static PurpleAccountUiOps _uiAccountOps;
	static PurpleEventLoopUiOps _uiEventLoopOps;
	static PurpleCoreUiOps _uiCoreOps;
	static PurpleConversationUiOps _uiConvOps;
	static PurpleBlistUiOps _uiBuddyOps;
	static PurpleXferUiOps _uiXferOps;
	static PurpleNotifyUiOps _uiNotifyOps;
	static PurplePrivacyUiOps _uiPrivacyOps;
	static PurpleRequestUiOps _uiRequestOps;
	static PurpleConnectionUiOps _uiConnectOps;
	static PurpleWhiteboardUiOps _uiWhiteboardOps;
	static PurpleDebugUiOps _uiDebugOps;

	static PurpleRequestFeature _features;
	static GHashTable* _uiInfo;
	static GRand* _gRand;

	static tthread::recursive_mutex _accountMutex;
	static std::map<PurpleAccount*, IMInvoker*> _accountInstances;
	static tthread::mutex _initMutex;
	static tthread::condition_variable _initCond;
	static DelayedEventQueue* _eventQueue;

	// libpurple event callbacks
	static void signedOnCB(PurpleConnection *gc, gpointer null);
	static void conversationCreatedCB(PurpleConversation *conv, void *data);
	static void chatJoinedCB(PurpleConversation *conv, void *data);
	static void chatJoinFailedCB(PurpleConnection *gc, GHashTable *components);
	static void buddyTypingCB(PurpleAccount *account, const char *name, void *data);
	static void buddyTypedCB(PurpleAccount *account, const char *name, void *data);
	static void buddyTypingStoppedCB(PurpleAccount *account, const char *name, void *data);
	static void buddyIdleChangedCB(PurpleBuddy *buddy, gboolean old_idle, gboolean idle, PurpleBuddyEvent event);
	static void blistNodeAliasedCB(PurpleBlistNode *node, char *old_alias);
	static void buddyEventCB(PurpleBuddy *buddy, PurpleBuddyEvent event);
	static void buddyStatusChangedCB(PurpleBuddy *buddy, PurpleStatus *oldstatus, PurpleStatus *newstatus, PurpleBuddyEvent event);
	static void buddyAddedCB(PurpleBuddy* buddy);
	static void buddyRemovedCB(PurpleBuddy* buddy);
	static void fileRecvRequestCB(PurpleXfer *xfer);
	static void buddyCapsChangedCB(PurpleBuddy* buddy, PurpleMediaCaps newcaps, PurpleMediaCaps oldcaps);

	// these are only being called from the delayed queue's thread
	static void initLibPurple(void *userdata, const std::string event);
	static void setupPurpleSignals();

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

	// libpurple debug
	static void purpleDebugPrint(PurpleDebugLevel level, const char *category, const char *arg_s);
	static gboolean purpleDebugIsEnabled(PurpleDebugLevel level, const char *category);


	// libpurple core operations
	static void purplePrefsInit(void);
	static void purpleDebugInit(void);
	static void purpleUIInit(void);
	static void purpleQuit(void);
	static GHashTable* purpleGetUIInfo(void);

	//libpurple conversation operations
	static void purpleCreateConversation(PurpleConversation *conv);
	static void purpleDestroyConversation(PurpleConversation *conv);
	static void purpleWriteChat(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime);
	static void purpleWriteIm(PurpleConversation *conv, const char *who, const char *message, PurpleMessageFlags flags, time_t mtime);
	static void purpleWriteConv(PurpleConversation *conv, const char *name, const char *alias, const char *message, PurpleMessageFlags flags, time_t mtime);
	static void purpleChatAddUsers(PurpleConversation *conv, GList *cbuddies, gboolean new_arrivals);
	static void purpleChatRenameUser(PurpleConversation *conv, const char *old_name, const char *new_name, const char *new_alias);
	static void purpleChatRemoveUsers(PurpleConversation *conv, GList *users);
	static void purpleChatUpdateUser(PurpleConversation *conv, const char *user);
	static void purplePresentConversation(PurpleConversation *conv);
	static gboolean purpleHasFocus(PurpleConversation *conv);
	static gboolean purpleCustomSmileyAdd(PurpleConversation *conv, const char *smile, gboolean remote);
	static void purpleCustomSmileyWrite(PurpleConversation *conv, const char *smile, const guchar *data, gsize size);
	static void purpleCustomSmileyClose(PurpleConversation *conv, const char *smile);
	static void purpleSendConfirm(PurpleConversation *conv, const char *message);

	// buddy operations
	static void purpleNewList(PurpleBuddyList *list);
	static void purpleNewNode(PurpleBlistNode *node);
	static void purpleShow(PurpleBuddyList *list);
	static void purpleUpdate(PurpleBuddyList *list, PurpleBlistNode *node);
	static void purpleRemove(PurpleBuddyList *list, PurpleBlistNode *node);
	static void purpleDestroy(PurpleBuddyList *list);
	static void purpleSetVisible(PurpleBuddyList *list, gboolean show);
	static void purpleRequestAddBuddy(PurpleAccount *account, const char *username, const char *group, const char *alias);
	static void purpleRequestAddChat(PurpleAccount *account, PurpleGroup *group, const char *alias, const char *name);
	static void purpleRequestAddGroup(void);
	static void purpleSaveNode(PurpleBlistNode *node);
	static void purpleRemoveNode(PurpleBlistNode *node);
	static void purpleSaveAccount(PurpleAccount *account);

	// file transfer operations
	static void purpleNewXfer(PurpleXfer *xfer);
	static void purpleDestroy(PurpleXfer *xfer);
	static void purpleAddXfer(PurpleXfer *xfer);
	static void purpleUpdateProgress(PurpleXfer *xfer, double percent);
	static void purpleCancelLocal(PurpleXfer *xfer);
	static void purpleCancelRemote(PurpleXfer *xfer);
	static gssize purpleWrite(PurpleXfer *xfer, const guchar *buffer, gssize size);
	static gssize purpleRead(PurpleXfer *xfer, guchar **buffer, gssize size);
	static void purpleDataNotSent(PurpleXfer *xfer, const guchar *buffer, gsize size);
	static void purpleAddThumbnail(PurpleXfer *xfer, const gchar *formats);

	// notification operations
	static void* purpeNotifyMessage(PurpleNotifyMsgType type, const char *title, const char *primary, const char *secondary, PurpleRequestCommonParameters *cpar);
	static void* purpeNotifyEmail(PurpleConnection *gc, const char *subject, const char *from, const char *to, const char *url);
	static void* purpeNotifyEmails(PurpleConnection *gc, size_t count, gboolean detailed, const char **subjects, const char **froms, const char **tos, const char **urls);
	static void* purpeNotifyFormatted(const char *title, const char *primary, const char *secondary, const char *text);
	static void* purpeNotifySearchResults(PurpleConnection *gc, const char *title, const char *primary, const char *secondary, PurpleNotifySearchResults *results, gpointer user_data);
	static void purpeNotifySearchResultsNewRows(PurpleConnection *gc, PurpleNotifySearchResults *results, void *data);
	static void* purpeNotifyUserInfo(PurpleConnection *gc, const char *who, PurpleNotifyUserInfo *user_info);
	static void* purpeNotifyURI(const char *uri);
	static void purpeNotifyClose(PurpleNotifyType type, void *ui_handle);

	// account operations
	static void accountNotifyAdded(PurpleAccount *account, const char *remote_user, const char *id, const char *alias, const char *message);
	static void accountStatusChanged(PurpleAccount *account, PurpleStatus *status);
	static void accountRequestAdd(PurpleAccount *account, const char *remote_user, const char *id, const char *alias, const char *message);
	static void* accountRequestAuthorize(PurpleAccount *account, const char *remote_user, const char *id, const char *alias, const char *message, gboolean on_list, PurpleAccountRequestAuthorizationCb authorize_cb, PurpleAccountRequestAuthorizationCb deny_cb, void *user_data);
	static void accountCloseRequest(void *ui_handle);

	// privacy ui operations
	static void purplePermitAdded(PurpleAccount *account, const char *name);
	static void purplePermitRemoved(PurpleAccount *account, const char *name);
	static void purpleDebyAdded(PurpleAccount *account, const char *name);
	static void purpleDenyRemoved(PurpleAccount *account, const char *name);

	// request ui operations
	static void* purpleRequestInput(const char *title, const char *primary,
	                                const char *secondary, const char *default_value,
	                                gboolean multiline, gboolean masked, gchar *hint,
	                                const char *ok_text, GCallback ok_cb,
	                                const char *cancel_text, GCallback cancel_cb,
	                                PurpleRequestCommonParameters *cpar, void *user_data);
	static void* purpleRequestChoice(const char *title, const char *primary,
	                                 const char *secondary, gpointer default_value,
	                                 const char *ok_text, GCallback ok_cb, const char *cancel_text,
	                                 GCallback cancel_cb, PurpleRequestCommonParameters *cpar,
	                                 void *user_data, va_list choices);
	static void* purpleRequestAction(const char *title, const char *primary,
	                                 const char *secondary, int default_action,
	                                 PurpleRequestCommonParameters *cpar, void *user_data,
	                                 size_t action_count, va_list actions);
	static void* purpleRequestWait(const char *title, const char *primary,
	                               const char *secondary, gboolean with_progress,
	                               PurpleRequestCancelCb cancel_cb,
	                               PurpleRequestCommonParameters *cpar, void *user_data);

	static void purpleRequestWaitUpdate(void *ui_handle, gboolean pulse, gfloat fraction);
	static void* purpleRequestFields(const char *title, const char *primary,
	                                 const char *secondary, PurpleRequestFields *fields,
	                                 const char *ok_text, GCallback ok_cb,
	                                 const char *cancel_text, GCallback cancel_cb,
	                                 PurpleRequestCommonParameters *cpar, void *user_data);
	static void* purpleRequestFile(const char *title, const char *filename,
	                               gboolean savedialog, GCallback ok_cb, GCallback cancel_cb,
	                               PurpleRequestCommonParameters *cpar, void *user_data);
	static void* purpleRequestFolder(const char *title, const char *dirname,
	                                 GCallback ok_cb, GCallback cancel_cb,
	                                 PurpleRequestCommonParameters *cpar, void *user_data);
	static void purpleRequestClose(PurpleRequestType type, void *ui_handle);


	// connection ui operations
	static void purpleConnectProgress(PurpleConnection *gc, const char *text, size_t step, size_t step_count);
	static void purpleConnected(PurpleConnection *gc);
	static void purpleDisonnected(PurpleConnection *gc);
	static void purpleNotice(PurpleConnection *gc, const char *text);
	static void purpleNetworkConnected(void);
	static void purpleNetworkDisconnected(void);
	static void purpleReportDisconnect(PurpleConnection *gc, PurpleConnectionError reason, const char *text);


	// whiteboard ui operations
	static void purpleCreateWB(PurpleWhiteboard *wb);
	static void purpleDestroyWB(PurpleWhiteboard *wb);
	static void purpleSetDimensions(PurpleWhiteboard *wb, int width, int height);
	static void purpleSetBrush(PurpleWhiteboard *wb, int size, int color);
	static void purpleDrawPont(PurpleWhiteboard *wb, int x, int y, int color, int size);
	static void purpleDrawLine(PurpleWhiteboard *wb, int x1, int y1, int x2, int y2, int color, int size);
	static void purpleClearWB(PurpleWhiteboard *wb);


	PurpleAccount* _account;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(IMInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: IMINVOKER_H_FNWG0XCQ */
