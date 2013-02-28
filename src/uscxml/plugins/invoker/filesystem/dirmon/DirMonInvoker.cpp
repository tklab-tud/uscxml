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
  _thread(NULL) {
}

DirMonInvoker::~DirMonInvoker() {
	_isRunning = false;
	if (_thread)
		_thread->join();
};

boost::shared_ptr<IOProcessorImpl> DirMonInvoker::create(Interpreter* interpreter) {
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
	if (req.params.find("dir") != req.params.end() && boost::iequals(req.params.find("reportexisting")->second, "false"))
		_reportExisting = false;
	if (req.params.find("recurse") != req.params.end() && boost::iequals(req.params.find("recurse")->second, "true"))
		_recurse = true;
	if (req.params.find("reporthidden") != req.params.end() && boost::iequals(req.params.find("reporthidden")->second, "true"))
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
		if (!_interpreter->toAbsoluteURI(url) || !boost::iequals(url.scheme(), "file")) {
			LOG(ERROR) << "Given directory '" << dirIter->second << "' cannot be transformed to absolute path";
		} else {
			_watchIds.insert(std::make_pair(url.path(), _fileWatcher.addWatch(url.path(), this, _recurse)));
		}
		dirIter++;
	}
	_isRunning = true;
	_thread = new tthread::thread(DirMonInvoker::run, this);
}

void DirMonInvoker::run(void* instance) {
	if (((DirMonInvoker*)instance)->_reportExisting)
		((DirMonInvoker*)instance)->reportExisting();

	while(((DirMonInvoker*)instance)->_isRunning)
		((DirMonInvoker*)instance)->_fileWatcher.update();
}

void DirMonInvoker::reportExisting() {
	std::multimap<std::string, FW::WatchID>::iterator watchIter = _watchIds.begin();
	while(watchIter != _watchIds.end()) {
		reportExistingIn(watchIter->first, watchIter->second);
		watchIter++;
	}
}

void DirMonInvoker::handleFileAction(FW::WatchID watchid, const FW::String& dir, const FW::String& filename, FW::Action action) {
  
  if (_suffixes.size() > 0) {
    bool validSuffix = false;
    std::set<std::string>::iterator suffixIter = _suffixes.begin();
    while(suffixIter != _suffixes.end()) {
      if (boost::algorithm::ends_with(filename, *suffixIter)) {
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
	case FW::Actions::Existing:
		event.name = "file.existing";
		break;
	case FW::Actions::Add:
		event.name = "file.added";
		break;
	case FW::Actions::Delete:
		event.name = "file.deleted";
		break;
	case FW::Actions::Modified:
		event.name = "file.modified";
		break;
	default:
		break;
	}

  // basename is the filename with suffix
	std::string basename;
	size_t lastSep;
	if ((lastSep = filename.find_last_of(PATH_SEPERATOR)) != std::string::npos) {
		lastSep++;
		basename = filename.substr(lastSep, filename.length() - lastSep);
  	event.data.compound["file"].compound["name"] = Data(basename, Data::VERBATIM);
	}
  
  // return if this is a hidden file
  if (boost::algorithm::starts_with(basename, ".") && !_reportHidden)
    return;

  struct stat fileStat;
	if (action != FW::Actions::Delete) {
    if (stat(filename.c_str(), &fileStat) != 0) {
      LOG(ERROR) << "Error with stat on directory entry " << filename << ": " << strerror(errno);
      return;
    } else {
      event.data.compound["file"].compound["mtime"] = toStr(fileStat.st_mtime);
      event.data.compound["file"].compound["ctime"] = toStr(fileStat.st_ctime);
      event.data.compound["file"].compound["atime"] = toStr(fileStat.st_atime);
      event.data.compound["file"].compound["size"]  = toStr(fileStat.st_size);
    }
  }

  // extension is the suffix and strippedName the basename without the suffix
	size_t lastDot;
	if ((lastDot = basename.find_last_of(".")) != std::string::npos) {
		std::string extension = basename.substr(lastDot + 1);
		event.data.compound["file"].compound["extension"] = Data(extension, Data::VERBATIM);
  	std::string strippedName = basename.substr(0, lastDot);
		event.data.compound["file"].compound["strippedName"] = Data(strippedName, Data::VERBATIM);
	}

  // relpath is the path to the file relative to the dir
	if (boost::algorithm::starts_with(filename, dir)) {
		std::string relPath = filename.substr(dir.length());
  	event.data.compound["file"].compound["relPath"] = Data(relPath, Data::VERBATIM);

    // relDir is the relpath without the basename
    if ((lastSep = relPath.find_last_of(PATH_SEPERATOR)) != std::string::npos) {
  		lastSep++;
      std::string relDir = relPath.substr(0, lastSep);
    	event.data.compound["file"].compound["relDir"] = Data(relDir, Data::VERBATIM);
  	}
	}

	event.data.compound["file"].compound["path"] = Data(filename, Data::VERBATIM);
	event.data.compound["file"].compound["dir"] = Data(dir, Data::VERBATIM);

	returnEvent(event);
}

bool DirMonInvoker::filter(const std::string filename) {
	return true;
}

void DirMonInvoker::reportExistingIn(const std::string dir, FW::WatchID watchid) {
#ifndef WIN32
	DIR *dp;
	dp = opendir(dir.c_str());
	if (dp == NULL) {
		LOG(ERROR) << "Error opening directory " << dir << ": " << strerror(errno);
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
	StringCchCopy(szDir, MAX_PATH, dir.c_str());
	StringCchCat(szDir, MAX_PATH, TEXT("\\*"));

	hFind = FindFirstFile(szDir, &ffd);
	do {
		std::string dname = ffd.cFileName;
#endif

		if (boost::iequals(dname, ".") || boost::iequals(dname, ".."))
			continue;

		char* filename = (char*)malloc(dir.size() + dname.size() + 2);
		sprintf(filename, "%s/%s", dir.c_str(), dname.c_str());

		struct stat fileStat;
		if (stat(filename, &fileStat) != 0) {
			LOG(ERROR) << "Error with stat on directory entry " << filename << ": " << strerror(errno);
			free(filename);
			continue;
		}

		if (fileStat.st_mode & S_IFDIR) {
			if (_recurse) {
				reportExistingIn(filename, watchid);
			} else {
				free(filename);
				continue;
			}
		}

		if (!filter(dname)) {
			free(filename);
			continue;
		}

		handleFileAction(watchid, dir, filename, FW::Actions::Existing);
#ifndef WIN32
	}
	closedir(dp);
#else
	}
	while (FindNextFile(hFind, &ffd) != 0);
	FindClose(hFind);
#endif

}

}