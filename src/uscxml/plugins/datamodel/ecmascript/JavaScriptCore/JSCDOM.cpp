#include "JSCDOM.h"

namespace Arabica {
namespace DOM {

JSCDOM::JSCDOM() {
	xpath = NULL;
	storage = NULL;
}

JSCDOM::~JSCDOM() {
	if (xpath)
		delete(xpath);
	if (storage)
		delete(storage);
}

}
}