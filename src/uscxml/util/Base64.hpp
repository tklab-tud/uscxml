// taken from http://www.adp-gmbh.ch/cpp/common/base64.html
#ifndef BASE64_H_5FKG12HF
#define BASE64_H_5FKG12HF

extern "C" {
#include "Base64.h"
}

#include <stdlib.h>
#include <string>
#include "uscxml/Common.h"

namespace uscxml {

USCXML_API inline std::string base64Encode(const char* data, unsigned int len, bool withBlockEnd = true) {
	base64_encodestate* ctx = (base64_encodestate*)malloc(sizeof(base64_encodestate));
	base64_init_encodestate(ctx);
	
	/**
	 * Wikipedia: Very roughly, the final size of Base64-encoded binary data is equal to 1.37
	 * times the original data size + 814 bytes (for headers). The size of the decoded data can
	 * be approximated with this formula:
	 */
	
	int written = 0;
	char* out = (char*)malloc(len * 1.4 + 814);
	written += base64_encode_block(data, len, out, ctx);
	if (withBlockEnd) {
		written += base64_encode_blockend(out + written, ctx);
		written--;  // drop the newline
	}
	std::string result(out, written);
	free(ctx);
	free(out);
	return result;
}

USCXML_API inline std::string base64Decode(const std::string& data) {
	base64_decodestate* ctx = (base64_decodestate*)malloc(sizeof(base64_decodestate));
	base64_init_decodestate(ctx);
	
	char* out = (char*)malloc(data.size());
	size_t size = base64_decode_block(data.data(), data.size(), out, ctx);
	free(ctx);
	std::string result(out, size);
	free(out);
	return result;
}

//	USCXML_API std::string base64Decode(const std::string& data);
//	USCXML_API std::string base64Encode(const char* data, unsigned int len);

}
#endif /* end of include guard: BASE64_H_5FKG12HF */
