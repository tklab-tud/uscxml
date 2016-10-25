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

#ifndef URL_H_9DAEGSMV
#define URL_H_9DAEGSMV

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"

#define DOWNLOAD_IF_NECESSARY if (!_isDownloaded) { download(true); }

#include <string>
#include <sstream>
#include <map>
#include <set>
#include <list>
#include <thread>
#include <condition_variable>
#include <curl/curl.h>
#include <uriparser/Uri.h>

#define USCXML_URI_STRING(obj, field) std::string(obj.field.first, obj.field.afterLast - obj.field.first)

namespace uscxml {

class URL;

class USCXML_API URLMonitor {
public:
	virtual void downloadStarted(const URL& url) {};
	virtual void downloadCompleted(const URL& url) {};
	virtual void downloadFailed(const URL& url, int errorCode) {};
	virtual void headerChunkReceived(const URL& url, const std::string& headerChunk) {};
	virtual void contentChunkReceived(const URL& url, const std::string& contentChunk) {};
};

enum URLRequestType {
	POST,
	GET
};

class USCXML_API URLImpl : public std::enable_shared_from_this<URLImpl> {
public:
	URLImpl(const std::string& url);
	~URLImpl();

	bool isAbsolute() const {
		// see https://sourceforge.net/p/uriparser/bugs/3/
		return _uri.absolutePath || ((_uri.hostText.first != nullptr) && (_uri.pathHead != nullptr));
	}

	std::string scheme() const {
		return USCXML_URI_STRING(_uri, scheme);
	}

	std::string userInfo() const {
		return USCXML_URI_STRING(_uri, userInfo);
	}

	std::string host() const {
		return USCXML_URI_STRING(_uri, hostText);
	}

	std::string port() const {
		return USCXML_URI_STRING(_uri, portText);
	}

	std::string fragment() const {
		return USCXML_URI_STRING(_uri, fragment);
	}

	std::map<std::string, std::string> query() const;
	std::string path() const;
	std::list<std::string> pathComponents() const;

	void normalize();

	static URL resolve(URLImpl* relativeURL, URLImpl* absoluteURL);
	static URL resolveWithCWD(URLImpl* relativeURL);
	static URL refer(URLImpl* absoluteSource, URLImpl* absoluteBase);

	void addMonitor(URLMonitor* monitor)    {
		_monitors.insert(monitor);
	}
	void removeMonitor(URLMonitor* monitor) {
		_monitors.erase(monitor);
	}

	// downloading / uploading
	void addOutHeader(const std::string& key, const std::string& value) {
		_outHeader[key] = value;
	}
	void setOutContent(const std::string& content) {
		_outContent = content;
		_requestType = URLRequestType::POST;
	}
	void setRequestType(URLRequestType requestType) {
		_requestType = requestType;

	}

	const std::map<std::string, std::string> getInHeaderFields() {
		DOWNLOAD_IF_NECESSARY
		return _inHeaders;
	}

	const std::string getInHeaderField(const std::string& key) {
		DOWNLOAD_IF_NECESSARY
		if (_inHeaders.find(key) != _inHeaders.end()) {
			return _inHeaders[key];
		}
		return "";
	}

	const std::string getStatusCode() const {
//        DOWNLOAD_IF_NECESSARY
		return _statusCode;
	}

	const std::string getStatusMessage() const {
//        DOWNLOAD_IF_NECESSARY
		return _statusMsg;
	}

	const std::string getInContent(bool forceReload = false) {
		if (forceReload)
			_isDownloaded = false;
		DOWNLOAD_IF_NECESSARY
		return _rawInContent.str();
	}

	const void download(bool blocking = false);

	operator Data() const;
	operator std::string() const;

protected:
	URLImpl();
	UriUriA _uri;
	std::string _orig;

	CURL* getCurlHandle();
	static size_t writeHandler(void *ptr, size_t size, size_t nmemb, void *userdata);
	static size_t headerHandler(void *ptr, size_t size, size_t nmemb, void *userdata);

	void downloadStarted();
	void downloadCompleted();
	void downloadFailed(CURLcode errorCode);

	static void prepareException(ErrorEvent& exception, int errorCode, const std::string& origUri, UriParserStateA* parser);

	CURL* _handle = NULL;
	std::stringstream _rawInContent;
	std::stringstream _rawInHeader;
	std::map<std::string, std::string> _inHeaders;

	std::string _outContent;
	std::map<std::string, std::string> _outHeader;
	URLRequestType _requestType;

	std::string _statusCode;
	std::string _statusMsg;
	bool _isDownloaded = false;
	bool _hasFailed = false;
	std::string _error;

	std::condition_variable_any _condVar;
	std::recursive_mutex _mutex;

	std::set<URLMonitor*> _monitors;

	friend class URLFetcher;
};

class USCXML_API URL {
public:
	PIMPL_OPERATORS(URL);

	URL(const std::string url) : _impl(new URLImpl(url)) {}

	bool isAbsolute() {
		return _impl->isAbsolute();
	}

	std::string scheme() {
		return _impl->scheme();
	}

	std::string userInfo() {
		return _impl->userInfo();
	}

	std::string host() {
		return _impl->host();
	}

	std::string port() {
		return _impl->port();
	}

	std::string fragment() {
		return _impl->fragment();
	}

	std::map<std::string, std::string> query() {
		return _impl->query();
	}

	std::string path() {
		return _impl->path();
	}

	std::list<std::string> pathComponents() {
		return _impl->pathComponents();
	}

	void normalize() {
		return _impl->normalize();
	}

	static URL resolve(URL relativeURL, URL absoluteURL) {
		return URLImpl::resolve(relativeURL._impl.get(), absoluteURL._impl.get());
	}

	static URL resolveWithCWD(URL relativeURL) {
		return URLImpl::resolveWithCWD(relativeURL._impl.get());
	}

	static URL refer(URL absoluteSource, URL absoluteBase) {
		return URLImpl::refer(absoluteSource._impl.get(), absoluteBase._impl.get());
	}

	void addOutHeader(const std::string& key, const std::string& value) {
		return _impl->addOutHeader(key, value);
	}

	void setOutContent(const std::string& content) {
		return _impl->setOutContent(content);
	}
	void setRequestType(URLRequestType requestType) {
		return _impl->setRequestType(requestType);
	}

	const std::map<std::string, std::string> getInHeaderFields() {
		return _impl->getInHeaderFields();
	}

	const std::string getInHeaderField(const std::string& key) {
		return _impl->getInHeaderField(key);
	}

	const std::string getStatusCode() const {
		return _impl->getStatusCode();
	}

	const std::string getStatusMessage() const {
		return _impl->getStatusMessage();
	}

	const std::string getInContent(bool forceReload = false) {
		return _impl->getInContent(forceReload);
	}

	const void download(bool blocking = false) const {
		return _impl->download(blocking);
	}

	void addMonitor(URLMonitor* monitor)    {
		return _impl->addMonitor(monitor);
	}
	void removeMonitor(URLMonitor* monitor) {
		return _impl->removeMonitor(monitor);
	}

	operator Data() const {
		return _impl->operator Data();
	}

	operator std::string() {
		return (*_impl.get());
	}

protected:
	std::shared_ptr<URLImpl> _impl;
	friend class URLFetcher;
};

class USCXML_API URLFetcher {
public:
	static void fetchURL(URL& url);
	static void breakURL(URL& url);

	void start();
	void stop();

protected:
	URLFetcher();
	~URLFetcher();

	static URLFetcher* _instance;
	static URLFetcher* getInstance();

	static void run(void* instance);
	void perform();

	std::thread* _thread;
	std::condition_variable_any _condVar;
	std::recursive_mutex _mutex;
	bool _isStarted;

	std::map<CURL*, URL> _handlesToURLs;
	std::map<CURL*, curl_slist*> _handlesToHeaders;
	CURLM* _multiHandle;
	char* _envProxy;
};

}

#endif /* end of include guard: URL_H_9DAEGSMV */
