#ifndef URL_H_27HPRH76
#define URL_H_27HPRH76

#include <string>
#include <sstream>
#include <curl/curl.h>

namespace uscxml {

enum fcurl_type_e {
  CFTYPE_NONE=0,
  CFTYPE_FILE=1,
  CFTYPE_CURL=2
};

struct fcurl_data
{
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

class URL {
public:
	URL(const std::string urlString) : _urlString(urlString) {}

private:
	std::string _urlString;
  friend std::ostream & operator<<(std::ostream &stream, const URL& p);
};

std::ostream & operator<<(std::ostream &stream, const URL& url);

}


#endif /* end of include guard: URL_H_27HPRH76 */
