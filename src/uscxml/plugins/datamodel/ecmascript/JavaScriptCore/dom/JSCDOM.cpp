#include "JSCDOM.h"

namespace Arabica {
namespace DOM {

JSCDOM::JSCDOM() {
	xpath = NULL;
}

JSCDOM::~JSCDOM() {
	if (xpath)
		delete(xpath);
}

}
}