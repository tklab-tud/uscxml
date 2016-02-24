#include "uscxml/util/Base64.hpp"
#include <assert.h>

#define SOURCE_LEN 10

int main(int argc, char** argv) {
	std::string data;
	std::string base64CPP;
	std::string base64C;

	char buffer[SOURCE_LEN];
	for (size_t i = 0; i < SOURCE_LEN; i++) {
		buffer[i] = (char)55;
	}

	base64C = uscxml::base64Encode(buffer, SOURCE_LEN);

}