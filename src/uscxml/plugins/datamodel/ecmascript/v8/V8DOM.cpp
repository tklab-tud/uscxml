#include "V8DOM.h"

namespace Arabica {
namespace DOM {

V8DOM::V8DOM() {
}

V8DOM::~V8DOM() {
	if (xpath)
		delete(xpath);
	if (storage)
		delete(storage);
}

}
}