#ifndef URL_H_27HPRH76
#define URL_H_27HPRH76

#include <string>
#include <sstream>
#include <curl/curl.h>

// use arabica URL parser
#include <io/uri.hpp>

namespace uscxml {

class URL {
public:
  URL() {}
  URL(const std::string uri) : _uri(uri) {}
  virtual ~URL();
  const bool toAbsolute(const std::string& baseUrl);
  const std::string asLocalFile(const std::string& suffix, bool reload = false);

  const bool isAbsolute() const       { return _uri.is_absolute(); }
  const std::string scheme() const    { return _uri.scheme(); }
  const std::string host() const      { return _uri.host(); }
  const std::string port() const      { return _uri.port(); }
  const std::string path() const      { return _uri.path(); }
  const std::string asString() const  { return _uri.as_string(); }
  
private:
  Arabica::io::URI _uri;
  std::string _localFile;
  friend std::ostream & operator<<(std::ostream &stream, const URL& p);
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
