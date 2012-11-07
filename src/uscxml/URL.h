#ifndef URL_H_27HPRH76
#define URL_H_27HPRH76

#include "Utilities.h"

namespace uscxml {

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
