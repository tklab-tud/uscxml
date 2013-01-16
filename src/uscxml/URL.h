#ifndef URL_H_27HPRH76
#define URL_H_27HPRH76

#include <string>
#include <sstream>
#include <curl/curl.h>

// use arabica URL parser
#include <io/uri.hpp>

#include <boost/shared_ptr.hpp>
#include <boost/enable_shared_from_this.hpp>

namespace uscxml {
  
class URLImpl : public boost::enable_shared_from_this<URLImpl> {
public:
  URLImpl() {}
  URLImpl(const std::string uri) : _uri(uri) {}
  virtual ~URLImpl();
  const bool toAbsoluteCwd();
  const bool toAbsolute(const std::string& baseUrl);
  const std::string asLocalFile(const std::string& suffix, bool reload = false);

  static boost::shared_ptr<URLImpl> toLocalFile(const std::string& content, const std::string& suffix);

  const bool isAbsolute() const       { return _uri.is_absolute(); }
  const std::string scheme() const    { return _uri.scheme(); }
  const std::string host() const      { return _uri.host(); }
  const std::string port() const      { return _uri.port(); }
  const std::string path() const      { return _uri.path(); }
  const std::string asString() const  { return _uri.as_string(); }
  
private:
  std::string getLocalFilename(const std::string& suffix);
  
  Arabica::io::URI _uri;
  std::string _localFile;
};

class URL {
public:
  URL() : _impl() {}
  URL(const std::string uri) : _impl(new URLImpl(uri)) {}
  URL(boost::shared_ptr<URLImpl> const impl) : _impl(impl) { }
	URL(const URL& other) : _impl(other._impl) { }
  virtual ~URL() {};

  static URL toLocalFile(const std::string& content, const std::string& suffix) {
    boost::shared_ptr<URLImpl> impl = URLImpl::toLocalFile(content, suffix);
    return URL(impl);
  }
  
  operator bool()                   const { return _impl;}
	bool operator< (const URL& other) const { return _impl < other._impl; }
  bool operator==(const URL& other) const { return _impl == other._impl; }
  bool operator!=(const URL& other) const { return _impl != other._impl; }
  URL& operator= (const URL& other)       { _impl = other._impl; return *this; }
  
  const bool toAbsoluteCwd() { return _impl->toAbsoluteCwd(); }
  const bool toAbsolute(const std::string& baseUrl) { return _impl->toAbsolute(baseUrl); }
  const bool toAbsolute(const URL& baseUrl) { return _impl->toAbsolute(baseUrl.asString()); }
  const std::string asLocalFile(const std::string& suffix, bool reload = false) { return _impl->asLocalFile(suffix, reload); }
  
  const bool isAbsolute() const       { return _impl->isAbsolute(); }
  const std::string scheme() const    { return _impl->scheme(); }
  const std::string host() const      { return _impl->host(); }
  const std::string port() const      { return _impl->port(); }
  const std::string path() const      { return _impl->path(); }
  const std::string asString() const  { return _impl->asString(); }

  friend std::ostream & operator<<(std::ostream &stream, const URL& p);
    
protected:
  boost::shared_ptr<URLImpl> _impl;
};
  
enum fcurl_type_e {
    CFTYPE_NONE=0,
    CFTYPE_FILE=1,
    CFTYPE_CURL=2
};

struct fcurl_data {
	enum fcurl_type_e type;     /* type of handle */
	union {
		CURL *curl;
		FILE *file;
	} handle;                   /* handle */

	char *buffer;               /* buffer to store cached data*/
	size_t buffer_len;          /* currently allocated buffers length */
	size_t buffer_pos;          /* end of data in buffer*/
	int still_running;          /* Is background url fetch still in progress */
};

typedef struct fcurl_data URL_FILE;

URL_FILE *url_fopen(const char *url,const char *operation);
int url_fclose(URL_FILE *file);
int url_feof(URL_FILE *file);
size_t url_fread(void *ptr, size_t size, size_t nmemb, URL_FILE *file);
char * url_fgets(char *ptr, size_t size, URL_FILE *file);
void url_rewind(URL_FILE *file);

std::ostream & operator<<(std::ostream &stream, const URL& url);

}


#endif /* end of include guard: URL_H_27HPRH76 */
