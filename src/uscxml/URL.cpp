#include "URL.h"
#include <glog/logging.h>
#include <algorithm>

namespace uscxml {
		
std::ostream & operator<<(std::ostream & stream, const URL& url) {

	std::string urlString = url._urlString;
	std::string fileURL = "file://";

	// strip file:// to support relative filenames
	if(urlString.substr(0, fileURL.size()) == fileURL) {
		urlString = urlString.substr(fileURL.size());
#ifdef _WIN32
		urlString = urlString.substr(0,1) + ":" + urlString.substr(1);
//		std::replace( urlString.begin(), urlString.end(), '/', '\\');
#endif
	}
	LOG(ERROR) << "Trying to open " << urlString;
	URL_FILE *handle = url_fopen(urlString.c_str(), "r");

  if(!handle) {
	  LOG(ERROR) << "Cannot open URL " << url._urlString;
		return stream;
  }
	
	int nread;
  char buffer[256];

  do {
    nread = url_fread(buffer, 1,sizeof(buffer), handle);
    stream.write(buffer, nread);
  } while(nread);

  url_fclose(handle);
	return stream;
}
	
	
}