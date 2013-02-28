#ifndef DIRMONINVOKER_H_W09J90F0
#define DIRMONINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>
#include "FileWatcher/FileWatcher.h"
#include <map>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class DirMonInvoker : public InvokerImpl, public FW::FileWatchListener {
public:
	DirMonInvoker();
	virtual ~DirMonInvoker();
	virtual boost::shared_ptr<IOProcessorImpl> create(Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("dirmon");
		names.insert("DirectoryMonitor");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#dirmon");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	void handleFileAction(FW::WatchID watchid, const FW::String& dir, const FW::String& filename, FW::Action action);
	void reportExisting();
	void reportExistingIn(const std::string dir, FW::WatchID watchid);
	virtual bool filter(const std::string filename);

	static void run(void* instance);

protected:
	bool _reportExisting;
	bool _reportHidden;
	bool _recurse;
  std::set<std::string> _suffixes;

	bool _isRunning;
	tthread::thread* _thread;
	FW::FileWatcher _fileWatcher;
	std::multimap<std::string, FW::WatchID> _watchIds;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(DirMonInvoker, Invoker);
#endif

}


#endif /* end of include guard: DIRMONINVOKER_H_W09J90F0 */
