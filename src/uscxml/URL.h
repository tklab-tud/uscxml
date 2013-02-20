#ifndef URL_H_9DAEGSMV
#define URL_H_9DAEGSMV

#include <curl/curl.h>
#include <string>
#include <iostream>
#include <sstream>
#include <map>
#include <set>
#include <boost/shared_ptr.hpp>
#include <boost/enable_shared_from_this.hpp>

#include "uscxml/concurrency/tinythread.h"

// use arabica URL parser
#include <io/uri.hpp>

namespace uscxml {

class URL;

class URLMonitor {
public:
	virtual void downloadStarted(const URL& url) {};
	virtual void downloadCompleted(const URL& url) {};
	virtual void downloadFailed(const URL& url, int errorCode) {};
	virtual void headerChunkReceived(const URL& url, const std::string& headerChunk) {};
	virtual void contentChunkReceived(const URL& url, const std::string& contentChunk) {};
};

class URLImpl : public boost::enable_shared_from_this<URLImpl> {
public:
	URLImpl(const std::string& url);
	~URLImpl();
	static boost::shared_ptr<URLImpl> toLocalFile(const std::string& content, const std::string& suffix);

	static size_t writeHandler(void *ptr, size_t size, size_t nmemb, void *userdata);
	static size_t headerHandler(void *ptr, size_t size, size_t nmemb, void *userdata);

	void addMonitor(URLMonitor* monitor)    {
		_monitors.insert(monitor);
	}
	void removeMonitor(URLMonitor* monitor) {
		_monitors.erase(monitor);
	}

	const bool isAbsolute()      const {
		return _uri.is_absolute();
	}
	const std::string scheme()   const {
		return _uri.scheme();
	}
	const std::string host()     const {
		return _uri.host();
	}
	const std::string port()     const {
		return _uri.port();
	}
	const std::string path()     const {
		return _uri.path();
	}
	const std::string asString() const {
		return _uri.as_string();
	}

	const bool toAbsoluteCwd();
	const bool toAbsolute(const std::string& baseUrl);
	const std::string asLocalFile(const std::string& suffix, bool reload = false);

	void addOutHeader(const std::string& key, const std::string& value) {
		_outHeader[key] = value;
	}
	void setOutContent(const std::string& content);
	void setRequestType(const std::string& requestType);

	const std::map<std::string, std::string> getInHeaderFields();
	const std::string getInContent(bool forceReload = false);
	const void download(bool blocking = false);

	void downloadStarted();
	void downloadCompleted();
	void downloadFailed(int errorCode);

	friend class URLFetcher;

protected:
	URLImpl()  : _handle(NULL), _isDownloaded(false), _hasFailed(false) {}
	std::string getLocalFilename(const std::string& suffix);

	std::string _outContent;
	std::map<std::string, std::string> _outHeader;
	std::string _requestType;

	CURL* _handle;
	std::stringstream _inContent;
	std::stringstream _inHeader;

	Arabica::io::URI _uri;
	bool _isDownloaded;
	bool _hasFailed;

	std::string _localFile;

	tthread::condition_variable _condVar;
	tthread::recursive_mutex _mutex;

	std::set<URLMonitor*> _monitors;
	typedef std::set<URLMonitor*>::iterator monIter_t;
};

class URL {
public:
	URL() : _impl() {}
	URL(const std::string url) : _impl(new URLImpl(url)) {}
	URL(boost::shared_ptr<URLImpl> const impl) : _impl(impl) { }
	URL(const URL& other) : _impl(other._impl) { }
	virtual ~URL() {};

	operator bool() const {
		return _impl;
	}
	bool operator< (const URL& other) const {
		return _impl < other._impl;
	}
	bool operator==(const URL& other) const {
		return _impl == other._impl;
	}
	bool operator!=(const URL& other) const {
		return _impl != other._impl;
	}
	URL& operator= (const URL& other)       {
		_impl = other._impl;
		return *this;
	}

	const std::map<std::string, std::string> getInHeaderFields() const {
		return _impl->getInHeaderFields();
	}
	const std::string getInContent() const {
		return _impl->getInContent();
	}
	const void download(bool blocking = false)   const {
		return _impl->download(blocking);
	}

	void addOutHeader(const std::string& key, const std::string& value) {
		_impl->addOutHeader(key, value);
	}
	void setRequestType(const std::string& requestType) {
		_impl->setRequestType(requestType);
	}
	void setOutContent(const std::string& content) {
		_impl->setOutContent(content);
	}

	const bool toAbsoluteCwd()                        {
		return _impl->toAbsoluteCwd();
	}
	const bool toAbsolute(const std::string& baseUrl) {
		return _impl->toAbsolute(baseUrl);
	}
	const bool toAbsolute(const URL& baseUrl)         {
		return _impl->toAbsolute(baseUrl.asString());
	}
	const std::string asLocalFile(const std::string& suffix, bool reload = false) {
		return _impl->asLocalFile(suffix, reload);
	}

	static URL toLocalFile(const std::string& content, const std::string& suffix) {
		boost::shared_ptr<URLImpl> impl = URLImpl::toLocalFile(content, suffix);
		return URL(impl);
	}

	void addMonitor(URLMonitor* monitor)    {
		_impl->addMonitor(monitor);
	}
	void removeMonitor(URLMonitor* monitor) {
		_impl->removeMonitor(monitor);
	}

	const bool isAbsolute()      const {
		return _impl->isAbsolute();
	}
	const std::string scheme()   const {
		return _impl->scheme();
	}
	const std::string host()     const {
		return _impl->host();
	}
	const std::string port()     const {
		return _impl->port();
	}
	const std::string path()     const {
		return _impl->path();
	}
	const std::string asString() const {
		return _impl->asString();
	}

	friend class URLFetcher;
	friend std::ostream & operator<<(std::ostream &stream, const URL& p);

protected:
	void downloadStarted() {
		return _impl->downloadStarted();
	}
	void downloadCompleted() {
		return _impl->downloadCompleted();
	}
	void downloadFailed(int errorCode) {
		return _impl->downloadFailed(errorCode);
	}

	boost::shared_ptr<URLImpl> _impl;
};

class URLFetcher {
public:
	URLFetcher();
	~URLFetcher();

	static void fetchURL(URL& url);
	static void breakURL(URL& url);

	void start();
	void stop();

protected:
	static URLFetcher* _instance;
	static URLFetcher* getInstance();

	static void run(void* instance);
	void perform();

	tthread::thread* _thread;
	tthread::condition_variable _condVar;
	tthread::recursive_mutex _mutex;
	bool _isStarted;

	std::map<CURL*, URL> _handlesToURLs;
	CURLM* _multiHandle;
};

}

#endif /* end of include guard: URL_H_9DAEGSMV */
