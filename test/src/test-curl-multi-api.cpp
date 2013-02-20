#include <curl/curl.h>
#include <glog/logging.h>
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
  URLImpl(const std::string& url) : _handle(NULL), _uri(url), _isDownloaded(false) {
    _handle = curl_easy_init();
    if (_handle != NULL) {
      CURLcode curlError;
      curlError = curl_easy_setopt(_handle, CURLOPT_URL, _uri.as_string().c_str());
      if (curlError != CURLE_OK)
        LOG(ERROR) << "Cannot set url to " << _uri.as_string() << ": " << curl_easy_strerror(curlError);

      curlError = curl_easy_setopt(_handle, CURLOPT_WRITEDATA, this);
      if (curlError != CURLE_OK)
        LOG(ERROR) << "Cannot register this as write userdata: " << curl_easy_strerror(curlError);

      curlError = curl_easy_setopt(_handle, CURLOPT_WRITEFUNCTION, URLImpl::writeHandler);
      if (curlError != CURLE_OK)
        LOG(ERROR) << "Cannot set write callback: " << curl_easy_strerror(curlError);
      
      curlError = curl_easy_setopt(_handle, CURLOPT_HEADERFUNCTION, URLImpl::headerHandler);
      if (curlError != CURLE_OK)
        LOG(ERROR) << "Cannot request header from curl: " << curl_easy_strerror(curlError);

      curlError = curl_easy_setopt(_handle, CURLOPT_HEADERDATA, this);
      if (curlError != CURLE_OK)
        LOG(ERROR) << "Cannot register this as header userdata: " << curl_easy_strerror(curlError);
    } else {
      LOG(ERROR) << "curl_easy_init returned NULL, this is bad!";
    }
  }
  
  ~URLImpl() {
    if (_handle != NULL)
      curl_easy_cleanup(_handle);
  }
  
  static size_t writeHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
    URLImpl* url = (URLImpl*)userdata;
    url->_content.write((char*)ptr, size * nmemb);
    return size * nmemb;
  }

  static size_t headerHandler(void *ptr, size_t size, size_t nmemb, void *userdata) {
    URLImpl* url = (URLImpl*)userdata;
    url->_header.write((char*)ptr, size * nmemb);
    return size * nmemb;
  }

  void addMonitor(URLMonitor* monitor)    { _monitors.insert(monitor); }
  void removeMonitor(URLMonitor* monitor) { _monitors.erase(monitor); }

  const bool isAbsolute()      const { return _uri.is_absolute(); }
	const std::string scheme()   const { return _uri.scheme(); }
	const std::string host()     const { return _uri.host(); }
	const std::string port()     const { return _uri.port(); }
	const std::string path()     const { return _uri.path(); }
	const std::string asString() const { return _uri.as_string(); }

  void downloadStarted() {
    std::cout << "Starting download of " << asString() << std::endl;
    _content.str("");
    _content.clear();
    _header.str("");
    _header.clear();
    monIter_t monIter = _monitors.begin();
    while(monIter != _monitors.end()) {
//      (*monIter)->downloadStarted(URL(shared_from_this()));
      monIter++;
    }
  }

  void downloadCompleted() {
    std::cout << "Finished loading " << asString() << " with " << _content.str().size() << " bytes" << std::endl;
    _isDownloaded = true;
  }

  void downloadFailed(int errorCode) {
    std::cout << "FAILED!" << strerror(errorCode) << std::endl;
  }

  std::string getHeader(bool forceReload = false) {
    return _header.str();
  }
  
  std::string getContent(bool forceReload = false) {
    return _content.str();
  }

  std::stringstream _content;
  std::stringstream _header;
  CURL* _handle;
  Arabica::io::URI _uri;
  bool _isDownloaded;
  
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
  
  operator bool() const { return _impl; }
	bool operator< (const URL& other) const { return _impl < other._impl; }
	bool operator==(const URL& other) const { return _impl == other._impl; }
	bool operator!=(const URL& other) const {
		return _impl != other._impl;
	}
	URL& operator= (const URL& other)       {
		_impl = other._impl;
		return *this;
	}

  std::string getHeader() { return _impl->getHeader(); }
  std::string getContent() { return _impl->getContent(); }
  
  const bool toAbsoluteCwd()                        { return _impl->toAbsoluteCwd(); }
	const bool toAbsolute(const std::string& baseUrl) { return _impl->toAbsolute(baseUrl); }
	const bool toAbsolute(const URL& baseUrl)         { return _impl->toAbsolute(baseUrl.asString()); }
	const std::string asLocalFile(const std::string& suffix, bool reload = false) { return _impl->asLocalFile(suffix, reload); }

  void addMonitor(URLMonitor* monitor)    { _impl->addMonitor(monitor); }
  void removeMonitor(URLMonitor* monitor) { _impl->removeMonitor(monitor); }

  const bool isAbsolute()      const { return _impl->isAbsolute(); }
	const std::string scheme()   const { return _impl->scheme(); }
	const std::string host()     const { return _impl->host(); }
	const std::string port()     const { return _impl->port(); }
	const std::string path()     const { return _impl->path(); }
	const std::string asString() const { return _impl->asString(); }

  friend class URLFetcher;
	friend std::ostream & operator<<(std::ostream &stream, const URL& p);

protected:
  void downloadStarted() { return _impl->downloadStarted(); }
  void downloadCompleted() { return _impl->downloadCompleted(); }
  void downloadFailed(int errorCode) { return _impl->downloadFailed(errorCode); }

	boost::shared_ptr<URLImpl> _impl;
};

class URLFetcher {
public:
  URLFetcher() {
    _multiHandle = curl_multi_init();
    start();
  }
  
  ~URLFetcher() {
    curl_multi_cleanup(_multiHandle);
    stop();
  }
  
  void fetchURL(URL& url) {
    tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    url.downloadStarted();
    _handlesToURLs[url._impl->_handle] = url;
    curl_multi_add_handle(_multiHandle, url._impl->_handle);
    _condVar.notify_all();
  }

  void breakURL(URL& url) {
    tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    if (_handlesToURLs.find(url._impl->_handle) != _handlesToURLs.end()) {
      url.downloadFailed(0);
      curl_multi_remove_handle(_multiHandle, url._impl->_handle);
      _handlesToURLs.erase(url._impl->_handle);
    }
  }

  void start() {
    tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    if (!_isStarted) {
      _isStarted = true;
      _thread = new tthread::thread(URLFetcher::run, this);
    }
  }
  
  void stop() {
    tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
    if (_isStarted) {
      _isStarted = false;
      _thread->join();
      delete _thread;
    }
  }

  static void run(void* instance) {
    URLFetcher* THIS = (URLFetcher*)instance;
    THIS->_mutex.lock();
    while(THIS->_isStarted) {
      if(THIS->_handlesToURLs.size() > 0) {
        THIS->_mutex.unlock();
        THIS->perform();
        THIS->_mutex.lock();
      }
      THIS->_condVar.wait(THIS->_mutex);
    }
    THIS->_mutex.unlock();
  }
  
  void perform() {

    CURLMsg *msg; /* for picking up messages with the transfer status */
    int msgsLeft; /* how many messages are left */
    int stillRunning;
    
    {
      tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
      curl_multi_perform(_multiHandle, &stillRunning);
    }

    do {
      struct timeval timeout;
      int rc; /* select() return code */
      
      fd_set fdread, fdwrite, fdexcep;
      FD_ZERO(&fdread); FD_ZERO(&fdwrite); FD_ZERO(&fdexcep);

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
        default: /* action */
        {
          tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
          curl_multi_perform(_multiHandle, &stillRunning);
        }
          break;
      }
      
      {
        tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
        while ((msg = curl_multi_info_read(_multiHandle, &msgsLeft))) {
          if (msg->msg == CURLMSG_DONE) {
            _handlesToURLs[msg->easy_handle].downloadCompleted();
            curl_multi_remove_handle(_multiHandle, msg->easy_handle);
            _handlesToURLs.erase(msg->easy_handle);
          } else {
            switch (msg->data.result) {
              case CURLM_OK:
                break;
              case CURLM_BAD_HANDLE:
              case CURLM_BAD_EASY_HANDLE:
              case CURLM_OUT_OF_MEMORY:
              case CURLM_INTERNAL_ERROR:
              case CURLM_BAD_SOCKET:
              case CURLM_UNKNOWN_OPTION:
              case CURLM_LAST:
                _handlesToURLs[msg->easy_handle].downloadFailed(msg->data.result);
                curl_multi_remove_handle(_multiHandle, msg->easy_handle);
                _handlesToURLs.erase(msg->easy_handle);
              default:
                break;
            }
          }
        }
      }
    } while(stillRunning && _isStarted);
    
  }
  
  tthread::condition_variable _condVar;
  tthread::thread* _thread;
	tthread::recursive_mutex _mutex;
  bool _isStarted;
  
  std::map<CURL*, URL> _handlesToURLs;
  CURLM* _multiHandle;
};


int main(int argc, char** argv) {
  URLFetcher fetcher;
  URL heise("http://www.heise.de");
  URL localFile("file:///Users/sradomski/Desktop/scxml.xsd");
  URL slashdot("http://slashdot.org");
  URL asdf("daf://localhost:234");
  URL bahn("http://www.bahn.de");

  fetcher.fetchURL(heise);
  fetcher.fetchURL(localFile);
  fetcher.fetchURL(asdf);
  fetcher.fetchURL(slashdot);
  fetcher.fetchURL(bahn);

  while(1) {}
}