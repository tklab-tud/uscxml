#ifndef XmlBridgeInvoker_H_W09J90F0
#define XmlBridgeInvoker_H_W09J90F0

#include <map>

#include "../uscxml/config.h"
#include <uscxml/Interpreter.h>
#include "bridgeconfig.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class XmlEventsMonitor;


/* one XmlBridgeSMIO for each datablock */
class XmlBridgeSMIO {
public:
	enum Action {
	    ADDED = 1,
	    MODIFIED = 2,
	    DELETED = 4,
	    EXISTING = 8
	};

	XmlBridgeSMIO(const BridgeConfig & xmlconfig) : _bridgeconf(xmlconfig), _initialization(false), _lastChecked(0) {}
	~XmlBridgeSMIO();

	void addMonitor(XmlEventsMonitor* monitor) {
		_monitors.insert(monitor);
	}
	void removeMonitor(XmlEventsMonitor* monitor) {
		_monitors.erase(monitor);
	}

	void receiveDBFrameID(const uint8_t datablockID, const string dbframeID);
	void receiveReplyID(const uint8_t datablockID, const string replyID);

	std::map<std::string, struct stat> getAllEntries() {
		std::map<std::string, struct stat> entries;
		entries.insert(_knownEntries.begin(), _knownEntries.end());

		std::map<std::string, XmlBridgeSMIO*>::iterator dirIter = _knownDirs.begin();
		while(dirIter != _knownDirs.end()) {
			std::map<std::string, struct stat> dirEntries = dirIter->second->getAllEntries();
			std::map<std::string, struct stat>::iterator dirEntryIter = dirEntries.begin();
			while(dirEntryIter != dirEntries.end()) {
				entries[dirIter->first + PATH_SEPERATOR + dirEntryIter->first] = dirEntryIter->second;
				dirEntryIter++;
			}
			dirIter++;
		}

		return entries;
	}

protected:
	/* second private constructor */
	XmlBridgeSMIO(const std::string& dir, const std::string& relDir) : _dir(dir), _relDir(relDir), _recurse(true), _lastChecked(0) {}

	std::string _dir;
	std::string _relDir;

	std::map<std::string, struct stat> _knownEntries;
	std::map<std::string, XmlBridgeSMIO*> _knownDirs;
	std::set<XmlEventsMonitor*> _monitors;
	typedef std::set<XmlEventsMonitor*> _monitors_t;

	bool _initialization;
	time_t _lastChecked;

	BridgeConfig& _bridgeconf;

};

class XmlEventsMonitor {
public:
	virtual bool handleChanges();

};

class XmlBridgeInvoker : public InvokerImpl, public XmlEventsMonitor {
public:
	XmlBridgeInvoker();
	virtual ~XmlBridgeInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("xmlbridge");
		names.insert("XmlEventsMonitor");
		names.insert("http://ajile.it/xmlbridge");ù
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	virtual void handleDBFrame(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat);
	virtual void handleReply(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat);

	static void run(void* instance);

protected:
	/*bool _reportExisting;
	bool _reportHidden;
	bool _recurse;*/

	/*std::string _dir;
	std::set<std::string> _suffixes;*/

	bool _isRunning;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;

	XmlBridgeSMIO* _watcher;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(XmlBridgeInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: XmlBridgeInvoker_H_W09J90F0 */
