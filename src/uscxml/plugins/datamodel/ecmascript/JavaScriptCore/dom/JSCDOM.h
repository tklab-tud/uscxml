#ifndef JSCDOM_H_1RC5LCG8
#define JSCDOM_H_1RC5LCG8

#include "uscxml/Interpreter.h"
#include <JavaScriptCore/JavaScriptCore.h>

#define JSC_DESTRUCTOR(type) \
static void jsDestructor(JSObjectRef object) { \
type* thing = static_cast<type*>(JSObjectGetPrivate(object)); \
delete thing->nativeObj; \
delete thing; \
}

namespace Arabica {
namespace DOM {

class JSCDOM {
public:
	JSCDOM();
	virtual ~JSCDOM() { };

	Arabica::XPath::XPath<std::string>* xpath;
};

}
}

#endif /* end of include guard: JSCDOM_H_1RC5LCG8 */
