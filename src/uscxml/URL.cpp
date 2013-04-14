#include <glog/logging.h>
#include "URL.h"

#include "uscxml/config.h"
#include <fstream>

#include <stdio.h>  /* defines FILENAME_MAX */
#ifdef _WIN32
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <io.h>
#include <direct.h>
#define getcwd _getcwd
#else
#include <unistd.h>
#endif

#include <cstdlib> // mkstemp
#ifdef HAS_UNISTD_H
#include <unistd.h>  // mkstemp legacy
#endif

#include <boost/algorithm/string.hpp>

namespace uscxml {

URLImpl::URLImpl(const std::string& url) : _handle(NULL), _uri(url), _isDownloaded(false), _hasFailed(false) {
	std::stringstream ss(_uri.path());
	std::string item;
	while(std::getline(ss, item, '/')) {
		if (item.length() == 0)
			continue;
		_pathComponents.push_back(item);
	}

}

URLImpl::~URLImpl() {
	if (_handle != NULL)
		curl_easy_cleanup(_handle);
}

CURL* URLImpl::getCurlHandle() {
	if (_handle == NULL) {
		_handle = curl_easy_init();
		if (_handle == NULL)
			LOG(ERROR) << "curl_easy_init returned NULL, this is bad!";
	}
	return _handle;
}

size_t URLImpl::writeHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
	URLImpl* url = (URLImpl*)userdata;
	url->_inContent.write((char*)ptr, size * nmemb);

	monIter_t monIter = url->_monitors.begin();
	while(monIter != url->_monitors.end()) {
		(*monIter)->contentChunkReceived(URL(url->shared_from_this()), std::string((char*)ptr, size * nmemb));
		monIter++;
	}

	return size * nmemb;
}

size_t URLImpl::headerHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
	URLImpl* url = (URLImpl*)userdata;
	url->_inHeader.write((char*)ptr, size * nmemb);

	monIter_t monIter = url->_monitors.begin();
	while(monIter != url->_monitors.end()) {
		(*monIter)->headerChunkReceived(URL(url->shared_from_this()), std::string((char*)ptr, size * nmemb));
		monIter++;
	}

	return size * nmemb;
}

void URLImpl::downloadStarted() {
//	LOG(INFO) << "Starting download of " << asString() << std::endl;
	_inContent.str("");
	_inContent.clear();
	_inHeader.str("");
	_inHeader.clear();

	monIter_t monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadStarted(URL(shared_from_this()));
		monIter++;
	}
}

void URLImpl::downloadCompleted() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

//	LOG(INFO) << "Finished downloading " << asString() << " with " << _inContent.str().size() << " bytes";

	_hasFailed = false;
	_isDownloaded = true;
	_condVar.notify_all();

	monIter_t monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadCompleted(URL(shared_from_this()));
		monIter++;
	}
}

void URLImpl::downloadFailed(CURLcode errorCode) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	LOG(ERROR) << "Downloading " << asString() << " failed: " << curl_easy_strerror(errorCode);

	_hasFailed = true;
	_isDownloaded = false;
	_condVar.notify_all();

	monIter_t monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		(*monIter)->downloadFailed(URL(shared_from_this()), errorCode);
		monIter++;
	}

}

const std::map<std::string, std::string> URLImpl::getInHeaderFields() {
	if (!_isDownloaded) {
		download(true);
	}

	std::map<std::string, std::string> headerFields;
	std::string line;
	while (std::getline(_inHeader, line)) {
		size_t colon = line.find_first_of(":");
		size_t newline = line.find_first_of("\r\n");
		if (newline == std::string::npos)
			newline = line.size();

		if (colon == std::string::npos) {
			if (headerFields.size() == 0) {
				// put http status in a key that can never occur otherwise
				headerFields["status:"] = line.substr(0, newline);
			} else {
				headerFields[line.substr(0, newline)] = line.substr(0, newline); // this should never happen
			}
		} else {
			std::string key = line.substr(0, colon);
			size_t firstChar = line.find_first_not_of(": ", colon, 2);
			if (firstChar == std::string::npos) {
				// nothing but spaces?
				headerFields[line.substr(0, newline)] = "";
			} else {
				std::string value = line.substr(firstChar, newline - firstChar);
				headerFields[key] = value;
			}
		}
	}

	return headerFields;
}

void URLImpl::setRequestType(const std::string& requestType) {
	_requestType = requestType;
}

void URLImpl::setOutContent(const std::string& content) {
	_outContent = content;
}

const std::string URLImpl::getInContent(bool forceReload) {
	if (!_isDownloaded) {
		download(true);
	}
	return _inContent.str();
}

const void URLImpl::download(bool blocking) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	if (_isDownloaded)
		return;

	URL url(shared_from_this());
	URLFetcher::fetchURL(url);

	if (blocking) {
		while(!_isDownloaded && !_hasFailed) {
			_condVar.wait(_mutex); // wait for notification
		}
	}
}

const bool URLImpl::toAbsoluteCwd() {
	char currPath[FILENAME_MAX];
	if (!getcwd(currPath, sizeof(currPath))) {
		return false;
	}
	currPath[sizeof(currPath) - 1] = '\0'; /* not really required */
#ifdef _WIN32
	return toAbsolute(std::string("file://" + std::string(currPath) + "/"));
#else
	return toAbsolute(std::string("file://" + std::string(currPath) + "/"));
#endif
}

std::string URLImpl::getLocalFilename(const std::string& suffix) {
	if (_localFile.length() > 0)
		return _localFile;

	if (_uri.scheme().compare("file") == 0)
		return _uri.path();

	// try hard to find a temporary directory
	const char* tmpDir = NULL;
	if (tmpDir == NULL)
		tmpDir = getenv("TMPDIR");
	if (tmpDir == NULL)
		tmpDir = getenv("TMP");
	if (tmpDir == NULL)
		tmpDir = getenv("TEMP");
	if (tmpDir == NULL)
		tmpDir = getenv("USERPROFILE");
	if (tmpDir == NULL)
		tmpDir = "/tmp/";

	char* tmpl = (char*)malloc(strlen(tmpDir) + 11 + suffix.length());
	char* writePtr = tmpl;
	memcpy(writePtr, tmpDir, strlen(tmpDir));
	writePtr += strlen(tmpDir);
	memcpy(writePtr, "scxmlXXXXXX", 11);
	writePtr += 11;
	memcpy(writePtr, suffix.c_str(), suffix.length());
	writePtr += suffix.length();
	tmpl[writePtr - tmpl] = 0;

#ifdef _WIN32
	_mktemp_s(tmpl, strlen(tmpl) + 1);
	int fd = _open(tmpl, _O_CREAT, _S_IREAD | _S_IWRITE);
#else
	int fd = mkstemps(tmpl, suffix.length());
#endif
	if (fd < 0) {
		LOG(ERROR) << "mkstemp " << tmpl << ": " << strerror(errno) << std::endl;
		return "";
	}
#ifdef WIN32
	_close(fd);
#else
	close(fd);
#endif
	return std::string(tmpl);
}

void URL::toBaseURL(URL& uri) {
	uri = asBaseURL(uri);
}

URL URL::asBaseURL(const URL& uri) {
	std::string uriStr = uri.asString();
	std::string baseUriStr = uriStr.substr(0, uriStr.find_last_of("/\\") + 1);
#ifdef _WIN32
	if (baseUriStr.find("file://") == 0) {
		baseUriStr = baseUriStr.substr(7);
	}
#endif
	return URL(baseUriStr);
}

	
const bool URLImpl::toAbsolute(const std::string& baseUrl) {
	if (_uri.is_absolute())
		return true;
	
	std::string uriStr = _uri.as_string();
#ifdef _WIN32
	if (baseUrl.find("file://") == 0) {
		_uri = Arabica::io::URI("file:///" + baseUrl.substr(7), _uri.as_string());
	} else {
		_uri = Arabica::io::URI(baseUrl, _uri.as_string());
	}
#else
	_uri = Arabica::io::URI(baseUrl, _uri.as_string());
#endif
	
	if (!_uri.is_absolute())
		return false;
	return true;
}

boost::shared_ptr<URLImpl> URLImpl::toLocalFile(const std::string& content, const std::string& suffix) {
	boost::shared_ptr<URLImpl> urlImpl = boost::shared_ptr<URLImpl>(new URLImpl());
	urlImpl->_localFile = urlImpl->getLocalFilename(suffix);
#ifdef _WIN32
	urlImpl->_uri = std::string("file://") + urlImpl->_localFile;
#else
	urlImpl->_uri = std::string("file://") + urlImpl->_localFile;
#endif
	std::ofstream file(urlImpl->_localFile.c_str(), std::ios_base::out);
	if(file.is_open()) {
		file << content;
		file.close();
	} else {
		return boost::shared_ptr<URLImpl>();
	}

	return urlImpl;
}

const std::string URLImpl::asLocalFile(const std::string& suffix, bool reload) {
	// this is already a local file
	if (_uri.scheme().compare("file") == 0)
		return _uri.path();

	if (_localFile.length() > 0 && !reload)
		return _localFile;

	if (_localFile.length() > 0)
		remove(_localFile.c_str());

	_localFile = getLocalFilename(suffix);

	std::ofstream file(_localFile.c_str(), std::ios_base::out);
	if(file.is_open()) {
		file << URL(this->shared_from_this());
		file.close();
	} else {
		_localFile = "";
	}

	return _localFile;
}

std::ostream & operator<<(std::ostream & stream, const URL& url) {
	URL nonConstUrl = url; // this is a hack
	stream << nonConstUrl.getInContent();
	return stream;
}

URLFetcher::URLFetcher() {
	_isStarted = false;
	_multiHandle = curl_multi_init();
	start();
}

URLFetcher::~URLFetcher() {
	stop();
	curl_multi_cleanup(_multiHandle);
}

void URLFetcher::fetchURL(URL& url) {
	URLFetcher* instance = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);

	CURL* handle = url._impl->getCurlHandle();
	assert(handle != NULL);
	if (handle == NULL)
		return;

	if (instance->_handlesToURLs.find(handle) == instance->_handlesToURLs.end()) {
		CURLcode curlError;

		(curlError = curl_easy_setopt(handle, CURLOPT_URL, url.asString().c_str())) == CURLE_OK ||
		LOG(ERROR) << "Cannot set url to " << url.asString() << ": " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_WRITEDATA, url._impl.get())) == CURLE_OK ||
		LOG(ERROR) << "Cannot register this as write userdata: " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_WRITEFUNCTION, URLImpl::writeHandler)) == CURLE_OK ||
		LOG(ERROR) << "Cannot set write callback: " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_HEADERFUNCTION, URLImpl::headerHandler)) == CURLE_OK ||
		LOG(ERROR) << "Cannot request header from curl: " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_HEADERDATA, url._impl.get())) == CURLE_OK ||
		LOG(ERROR) << "Cannot register this as header userdata: " << curl_easy_strerror(curlError);

		(curlError = curl_easy_setopt(handle, CURLOPT_SSL_VERIFYPEER, false)) == CURLE_OK ||
		LOG(ERROR) << "Cannot forfeit peer verification: " << curl_easy_strerror(curlError);


		if (boost::iequals(url._impl->_requestType, "post")) {

			(curlError = curl_easy_setopt(handle, CURLOPT_POST, 1)) == CURLE_OK ||
			LOG(ERROR) << "Cannot set request type to post for " << url.asString() << ": " << curl_easy_strerror(curlError);

			(curlError = curl_easy_setopt(handle, CURLOPT_COPYPOSTFIELDS, url._impl->_outContent.c_str())) == CURLE_OK ||
			LOG(ERROR) << "Cannot set post data " << url.asString() << ": " << curl_easy_strerror(curlError);

			struct curl_slist* headers = NULL;
			std::map<std::string, std::string>::iterator paramIter = url._impl->_outHeader.begin();
			while(paramIter != url._impl->_outHeader.end()) {
				char* key = curl_easy_escape(handle, paramIter->first.c_str(), paramIter->first.length());
				char* value = curl_easy_escape(handle, paramIter->second.c_str(), paramIter->second.length());

				char* header = (char*)malloc(paramIter->first.size() + strlen(value) + 3);
				sprintf(header,"%s: %s", paramIter->first.c_str(), value);
				headers = curl_slist_append(headers, header);

				curl_free(key);
				curl_free(value);
				paramIter++;
			}
			(curlError = curl_easy_setopt(handle, CURLOPT_HTTPHEADER, headers)) == CURLE_OK ||
			LOG(ERROR) << "Cannot headers for " << url.asString() << ": " << curl_easy_strerror(curlError);

			//curl_slist_free_all(headers);


		} else if (boost::iequals(url._impl->_requestType, "get")) {
			(curlError = curl_easy_setopt(handle, CURLOPT_HTTPGET, 1)) == CURLE_OK ||
			LOG(ERROR) << "Cannot set request type to get for " << url.asString() << ": " << curl_easy_strerror(curlError);
		}

		url.downloadStarted();
		instance->_handlesToURLs[handle] = url;
		assert(instance->_handlesToURLs.size() > 0);

		curl_multi_add_handle(instance->_multiHandle, handle);
		instance->_condVar.notify_all();
	}
}

void URLFetcher::breakURL(URL& url) {
	URLFetcher* instance = getInstance();
	CURL* handle = url._impl->getCurlHandle();

	tthread::lock_guard<tthread::recursive_mutex> lock(instance->_mutex);
	if (instance->_handlesToURLs.find(handle) != instance->_handlesToURLs.end()) {
		url.downloadFailed(CURLE_OK);
		curl_multi_remove_handle(instance->_multiHandle, handle);
		instance->_handlesToURLs.erase(handle);
	}
}

void URLFetcher::start() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (!_isStarted) {
		_isStarted = true;
		_thread = new tthread::thread(URLFetcher::run, this);
	}
}

void URLFetcher::stop() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (_isStarted) {
		_isStarted = false;
		_thread->join();
		delete _thread;
	}
}

void URLFetcher::run(void* instance) {
	URLFetcher* fetcher = (URLFetcher*)instance;
	while(fetcher->_isStarted) {
		fetcher->perform();
	}
	LOG(ERROR) << "URLFetcher thread stopped!";
}

void URLFetcher::perform() {

	CURLMsg *msg; /* for picking up messages with the transfer status */
	int msgsLeft; /* how many messages are left */
	int stillRunning;

	{
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		if (_handlesToURLs.empty()) {
			_condVar.wait(_mutex);
		}
		curl_multi_perform(_multiHandle, &stillRunning);
	}

	do {
		struct timeval timeout;
		int rc; /* select() return code */

		fd_set fdread, fdwrite, fdexcep;
		FD_ZERO(&fdread);
		FD_ZERO(&fdwrite);
		FD_ZERO(&fdexcep);

		int maxfd = -1;
		long curlTimeOut = -1;

		/* set a suitable timeout to play around with */
		timeout.tv_sec = 1;
		timeout.tv_usec = 0;

		{
			tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
			curl_multi_timeout(_multiHandle, &curlTimeOut);
		}

		if(curlTimeOut >= 0) {
			timeout.tv_sec = curlTimeOut / 1000;
			if(timeout.tv_sec > 1)
				timeout.tv_sec = 1;
			else
				timeout.tv_usec = (curlTimeOut % 1000) * 1000;
		}

		/* get file descriptors from the transfers */
		{
			tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
			curl_multi_fdset(_multiHandle, &fdread, &fdwrite, &fdexcep, &maxfd);
		}

		rc = select(maxfd+1, &fdread, &fdwrite, &fdexcep, &timeout);

		switch(rc) {
		case -1:
			/* select error */
			break;
		case 0: /* timeout */
		default: { /* action */
			tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
			curl_multi_perform(_multiHandle, &stillRunning);
		}
		break;
		}

		{
			tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
			while ((msg = curl_multi_info_read(_multiHandle, &msgsLeft))) {
				if (msg->msg == CURLMSG_DONE) {
					switch (msg->data.result) {
					case CURLM_OK:
						_handlesToURLs[msg->easy_handle].downloadCompleted();
						curl_multi_remove_handle(_multiHandle, msg->easy_handle);
						_handlesToURLs.erase(msg->easy_handle);
						break;
					default:
						LOG(ERROR) << "Unhandled curl status";
					case CURLM_BAD_HANDLE:
					case CURLM_BAD_EASY_HANDLE:
					case CURLE_FILE_COULDNT_READ_FILE:
					case CURLM_OUT_OF_MEMORY:
					case CURLM_INTERNAL_ERROR:
					case CURLM_BAD_SOCKET:
					case CURLM_UNKNOWN_OPTION:
					case CURLM_LAST:
						_handlesToURLs[msg->easy_handle].downloadFailed(msg->data.result);
						curl_multi_remove_handle(_multiHandle, msg->easy_handle);
						_handlesToURLs.erase(msg->easy_handle);
						break;
					}
				} else {
					LOG(ERROR) << "Curl reports info on unfinished download?!";
				}
			}
		}
	} while(stillRunning && _isStarted);
}

URLFetcher* URLFetcher::_instance = NULL;

URLFetcher* URLFetcher::getInstance() {
	if (_instance == NULL) {
		_instance = new URLFetcher();
	}
	return _instance;
}

}