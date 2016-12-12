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

#ifndef DIRMONINVOKER_H_W09J90F0
#define DIRMONINVOKER_H_W09J90F0

#include "uscxml/plugins/InvokerImpl.h"

#include <map>
#include <set>
#include <sys/stat.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class DirectoryWatchMonitor;

class DirectoryWatch {
public:
	enum Action {
		ADDED = 1,
		MODIFIED = 2,
		DELETED = 4,
		EXISTING = 8
	};

	DirectoryWatch(const std::string& dir, bool recurse = false) : _dir(dir), _recurse(recurse), _lastChecked(0) {}
	~DirectoryWatch();

	void addMonitor(DirectoryWatchMonitor* monitor) {
		_monitors.insert(monitor);
	}
	void removeMonitor(DirectoryWatchMonitor* monitor) {
		_monitors.erase(monitor);
	}
	void updateEntries(bool reportAsExisting = false);
	void reportAsDeleted();

	std::map<std::string, struct stat> getAllEntries() {
		std::map<std::string, struct stat> entries;
		entries.insert(_knownEntries.begin(), _knownEntries.end());

		std::map<std::string, DirectoryWatch*>::iterator dirIter = _knownDirs.begin();
		while(dirIter != _knownDirs.end()) {
			std::map<std::string, struct stat> dirEntries = dirIter->second->getAllEntries();
			std::map<std::string, struct stat>::iterator dirEntryIter = dirEntries.begin();
			while(dirEntryIter != dirEntries.end()) {
				entries[dirIter->first + '/' + dirEntryIter->first] = dirEntryIter->second;
				dirEntryIter++;
			}
			dirIter++;
		}

		return entries;
	}

	void setLogger(Logger logger) {
		_logger = logger;
	}

protected:
	DirectoryWatch(const std::string& dir, const std::string& relDir) : _dir(dir), _relDir(relDir), _recurse(true), _lastChecked(0) {}

	std::string _dir;
	std::string _relDir;
	Logger _logger;

	bool _recurse;
	std::map<std::string, struct stat> _knownEntries;
	std::map<std::string, DirectoryWatch*> _knownDirs;
	std::set<DirectoryWatchMonitor*> _monitors;
	typedef std::set<DirectoryWatchMonitor*> _monitors_t;
	time_t _lastChecked;
};

class DirectoryWatchMonitor {
public:
	virtual void handleChanges(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat) = 0;
};

class DirMonInvoker : public InvokerImpl, public DirectoryWatchMonitor {
public:
	DirMonInvoker();
	virtual ~DirMonInvoker();
	virtual std::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("dirmon");
		names.push_back("DirectoryMonitor");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#dirmon");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void eventFromSCXML(const Event& event);
	virtual void invoke(const std::string& source, const Event& invokeEvent);
	virtual void uninvoke();

	virtual void handleChanges(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat);

	static void run(void* instance);

protected:
	bool _reportExisting;
	bool _reportHidden;
	bool _recurse;

	std::string _dir;
	std::set<std::string> _suffixes;

	bool _isRunning;
	std::thread* _thread;
	std::recursive_mutex _mutex;

	DirectoryWatch* _watcher;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(DirMonInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: DIRMONINVOKER_H_W09J90F0 */
