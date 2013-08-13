#include "DirMonInvoker.h"
#include <glog/logging.h>

#include "uscxml/config.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include <sys/stat.h>
#ifndef WIN32
#include <dirent.h>
#else
#include <strsafe.h>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new DirMonInvokerProvider() );
	return true;
}
#endif

DirMonInvoker::DirMonInvoker() :
	_reportExisting(true),
	_reportHidden(false),
	_recurse(false),
	_thread(NULL),
	_watcher(NULL) {
}

DirMonInvoker::~DirMonInvoker() {
	_isRunning = false;
	if (_thread) {
		_thread->join();
		delete _thread;
	}
	if (_watcher)
		delete(_watcher);
};

boost::shared_ptr<InvokerImpl> DirMonInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<DirMonInvoker> invoker = boost::shared_ptr<DirMonInvoker>(new DirMonInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data DirMonInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void DirMonInvoker::send(const SendRequest& req) {
}

void DirMonInvoker::cancel(const std::string sendId) {
}

void DirMonInvoker::invoke(const InvokeRequest& req) {
	if (req.params.find("dir") == req.params.end()) {
		LOG(ERROR) << "No dir param given";
		return;
	}

	if (boost::iequals(req.params.find("reportexisting")->second, "false"))
		_reportExisting = false;
	if (req.params.find("recurse") != req.params.end() &&
	        boost::iequals(req.params.find("recurse")->second, "true"))
		_recurse = true;
	if (req.params.find("reporthidden") != req.params.end() &&
	        boost::iequals(req.params.find("reporthidden")->second, "true"))
		_reportHidden = true;

	std::string suffixList;
	if (req.params.find("suffix") != req.params.end()) {
		suffixList = req.params.find("suffix")->second;
	} else if (req.params.find("suffixes") != req.params.end()) {
		suffixList = req.params.find("suffixes")->second;
	}

	if (suffixList.size() > 0) {
		// seperate path into components
		std::stringstream ss(suffixList);
		std::string item;
		while(std::getline(ss, item, ' ')) {
			if (item.length() == 0)
				continue;
			_suffixes.insert(item);
		}
	}

	std::multimap<std::string, std::string>::const_iterator dirIter = req.params.find("dir");
	while(dirIter != req.params.upper_bound("dir")) {
		URL url(dirIter->second);
		if (!url.toAbsolute(_interpreter->getBaseURI()) || !boost::iequals(url.scheme(), "file")) {
			LOG(ERROR) << "Given directory '" << dirIter->second << "' cannot be transformed to absolute path";
		} else {
			_dir = url.path();
		}
		break;
	}

	_watcher = new DirectoryWatch(_dir, _recurse);
	_watcher->addMonitor(this);
	_watcher->updateEntries(true);

	_isRunning = true;
	_thread = new tthread::thread(DirMonInvoker::run, this);
}

void DirMonInvoker::run(void* instance) {
	while(((DirMonInvoker*)instance)->_isRunning) {
		((DirMonInvoker*)instance)->_watcher->updateEntries();
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
	}
}

void DirMonInvoker::handleChanges(DirectoryWatch::Action action, const std::string reportedDir, const std::string reportedFilename, struct stat fileStat) {

//  std::cout << action << " on " << reportedFilename << std::endl;

	std::string path;         // complete path to the file including filename
	std::string relPath;      // path relative to monitored directory including filename
	std::string dir;          // the name of the directory we monitor
	std::string relDir;       // the directory from dir to the actual directory where we found a file
	std::string basename;     // filename including suffix
	std::string strippedName; // filename without the suffix
	std::string extension;    // the extension

	dir = reportedDir;

	path = dir + reportedFilename;
	boost::algorithm::replace_all(path, "\\", "/");
	boost::algorithm::replace_all(path, "//", "/");

	assert(boost::algorithm::starts_with(path, dir));
	relPath = path.substr(dir.length());
	assert(boost::equal(path, dir + relPath));

	size_t lastSep;
	if ((lastSep = path.find_last_of(PATH_SEPERATOR)) != std::string::npos) {
		lastSep++;
		basename = path.substr(lastSep, path.length() - lastSep);
	} else {
		assert(false);
	}
	assert(boost::algorithm::ends_with(relPath, basename));

	// extension is the suffix and strippedName the basename without the suffix
	size_t lastDot;
	if ((lastDot = basename.find_last_of(".")) != std::string::npos) {
		if (lastDot == 0) {
			// hidden file
			strippedName = basename;
		} else {
			extension = basename.substr(lastDot + 1);
			strippedName = basename.substr(0, lastDot);
		}
	} else {
		strippedName = basename;
	}

	relDir = relPath.substr(0, relPath.length() - basename.length());
	assert(boost::equal(path, dir + relDir + basename));

	// return if this is a hidden file
	if (boost::algorithm::starts_with(basename, ".") && !_reportHidden)
		return;

	// ilter suffixes
	if (_suffixes.size() > 0) {
		bool validSuffix = false;
		std::set<std::string>::iterator suffixIter = _suffixes.begin();
		while(suffixIter != _suffixes.end()) {
			if (boost::algorithm::ends_with(path, *suffixIter)) {
				validSuffix = true;
				break;
			}
			suffixIter++;
		}
		if (!validSuffix)
			return;
	}

	Event event;
	event.invokeid = _invokeId;

	switch (action) {
	case DirectoryWatch::EXISTING:
		event.name = "file.existing";
		break;
	case DirectoryWatch::ADDED:
		event.name = "file.added";
		break;
	case DirectoryWatch::DELETED:
		event.name = "file.deleted";
		break;
	case DirectoryWatch::MODIFIED:
		event.name = "file.modified";
		break;
	default:
		break;
	}

	if (action != DirectoryWatch::DELETED) {
		event.data.compound["file"].compound["mtime"] = toStr(fileStat.st_mtime);
		event.data.compound["file"].compound["ctime"] = toStr(fileStat.st_ctime);
		event.data.compound["file"].compound["atime"] = toStr(fileStat.st_atime);
		event.data.compound["file"].compound["size"]  = toStr(fileStat.st_size);
	}

	event.data.compound["file"].compound["name"] = Data(basename, Data::VERBATIM);
	event.data.compound["file"].compound["extension"] = Data(extension, Data::VERBATIM);
	event.data.compound["file"].compound["strippedName"] = Data(strippedName, Data::VERBATIM);
	event.data.compound["file"].compound["relPath"] = Data(relPath, Data::VERBATIM);
	event.data.compound["file"].compound["relDir"] = Data(relDir, Data::VERBATIM);
	event.data.compound["file"].compound["path"] = Data(path, Data::VERBATIM);
	event.data.compound["file"].compound["dir"] = Data(dir, Data::VERBATIM);

	returnEvent(event);
}

DirectoryWatch::~DirectoryWatch() {
	std::map<std::string, DirectoryWatch*>::iterator dirIter = _knownDirs.begin();
	while(dirIter != _knownDirs.end()) {
		delete(dirIter->second);
		dirIter++;
	}

}

void DirectoryWatch::reportAsDeleted() {
	std::map<std::string, struct stat>::iterator fileIter = _knownEntries.begin();
	while(fileIter != _knownEntries.end()) {
		if (fileIter->second.st_mode & S_IFDIR) {
			_knownDirs[fileIter->first]->reportAsDeleted();
			delete _knownDirs[fileIter->first];
			_knownDirs.erase(fileIter->first);
		} else {
			_monitors_t::iterator monIter = _monitors.begin();
			while(monIter != _monitors.end()) {
				(*monIter)->handleChanges(DELETED, _dir, _relDir + PATH_SEPERATOR + fileIter->first, fileIter->second);
				monIter++;
			}
		}
		_knownEntries.erase(fileIter->first);
		fileIter++;
	}
	assert(_knownDirs.size() == 0);
	assert(_knownEntries.size() == 0);
}

void DirectoryWatch::updateEntries(bool reportAsExisting) {
	_monitors_t::iterator monIter;
	if (_dir[_dir.length() - 1] == PATH_SEPERATOR)
		_dir = _dir.substr(0, _dir.length() - 1);

	// stat directory for modification date
	struct stat dirStat;
	if (stat((_dir + _relDir).c_str(), &dirStat) != 0) {
		LOG(ERROR) << "Error with stat on directory " << _dir << ": " << strerror(errno);
		return;
	}

	if ((unsigned)dirStat.st_mtime >= (unsigned)_lastChecked) {
		// there are changes in the directory
		std::set<std::string> currEntries;

#ifndef WIN32
		DIR *dp;
		dp = opendir((_dir + _relDir).c_str());
		if (dp == NULL) {
			LOG(ERROR) << "Error opening directory " << _dir + _relDir << ": " << strerror(errno);
			return;
		}
		// iterate all entries and see what changed
		struct dirent* entry;
		while((entry = readdir(dp))) {
			std::string dname = entry->d_name;
#else
		WIN32_FIND_DATA ffd;
		HANDLE hFind = INVALID_HANDLE_VALUE;
		TCHAR szDir[MAX_PATH];
		StringCchCopy(szDir, MAX_PATH, _dir.c_str());
		StringCchCat(szDir, MAX_PATH, TEXT("\\*"));

		hFind = FindFirstFile(szDir, &ffd);
		do {
			std::string dname = ffd.cFileName;
#endif

			// see if the file was changed
			std::string filename = _dir + _relDir + "/" + dname;
//			asprintf(&filename, "%s/%s", (_dir + _relDir).c_str(), dname.c_str());

			struct stat fileStat;
			if (stat(filename.c_str(), &fileStat) != 0) {
				LOG(ERROR) << "Error with stat on directory entry: " << filename << ": " << strerror(errno);
				continue;
			}

			if (fileStat.st_mode & S_IFDIR) {
				if (boost::equals(dname, ".") || boost::equals(dname, "..")) {
					continue; // do not report . or ..
				}
			}

			currEntries.insert(dname);

			if (_knownEntries.find(dname) != _knownEntries.end()) {
				// we have seen this entry before
				struct stat oldStat = _knownEntries[dname];
				if (oldStat.st_mtime < fileStat.st_mtime) {
					monIter = _monitors.begin();
					while(monIter != _monitors.end()) {
						(*monIter)->handleChanges(MODIFIED, _dir, _relDir + PATH_SEPERATOR + dname, fileStat);
						monIter++;
					}
				}
			} else {
				// we have not yet seen this entry
				if (fileStat.st_mode & S_IFDIR) {
					_knownDirs[dname] = new DirectoryWatch(_dir, _relDir + PATH_SEPERATOR + dname);
					monIter = _monitors.begin();
					while(monIter != _monitors.end()) {
						_knownDirs[dname]->addMonitor(*monIter);
						monIter++;
					}
				} else {
					monIter = _monitors.begin();
					while(monIter != _monitors.end()) {
						if (reportAsExisting) {
							(*monIter)->handleChanges(EXISTING, _dir, _relDir + PATH_SEPERATOR + dname, fileStat);
						} else {
							(*monIter)->handleChanges(ADDED, _dir, _relDir + PATH_SEPERATOR + dname, fileStat);
						}
						monIter++;
					}
				}
			}

			_knownEntries[dname] = fileStat; // gets copied on insertion
#ifndef WIN32
		}
		closedir(dp);
#else
		}
		while (FindNextFile(hFind, &ffd) != 0);
		FindClose(hFind);
#endif
		// are there any known entries we have not seen this time around?
		std::map<std::string, struct stat>::iterator fileIter = _knownEntries.begin();
		while(fileIter != _knownEntries.end()) {
			if (currEntries.find(fileIter->first) == currEntries.end()) {
				// we used to know this file
				if (fileIter->second.st_mode & S_IFDIR) {
					if (_recurse) {
						_knownDirs[fileIter->first]->reportAsDeleted();
						delete _knownDirs[fileIter->first];
						_knownDirs.erase(fileIter->first);
					}
				} else {
					monIter = _monitors.begin();
					while(monIter != _monitors.end()) {
						(*monIter)->handleChanges(DELETED, _dir, _relDir + PATH_SEPERATOR + fileIter->first, fileIter->second);
						monIter++;
					}
				}
				_knownEntries.erase(fileIter++);
			} else {
				fileIter++;
			}
		}
		// remember when we last checked the directory for modifications
#ifndef WIN32
		time(&_lastChecked);
#else
		// TODO: this will fail with sub-millisecond updates to the directory
		_lastChecked = dirStat.st_mtime + 1;
#endif
		// update all directories
	}
	if (_recurse) {
		std::map<std::string, DirectoryWatch*>::iterator dirIter = _knownDirs.begin();
		while(dirIter != _knownDirs.end()) {
			dirIter->second->updateEntries();
			dirIter++;
		}
	}
}

}