// taken from http://www.adp-gmbh.ch/cpp/common/base64.html
#ifndef BASE64_H_5FKG12HF
#define BASE64_H_5FKG12HF

#include <string>

namespace uscxml {

std::string base64_encode(char const* , unsigned int len);
std::string base64_decode(std::string const& s);

}

#endif /* end of include guard: BASE64_H_5FKG12HF */
