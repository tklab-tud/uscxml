#ifndef JSCDOM_H_1RC5LCG8
#define JSCDOM_H_1RC5LCG8

#include "uscxml/Interpreter.h"
#include <JavaScriptCore/JavaScriptCore.h>
#include <XPath/XPath.hpp>
#include "../Storage.h"

#define JSC_DESTRUCTOR(type) \
static void jsDestructor(JSObjectRef object) { \
	type* thing = static_cast<type*>(JSObjectGetPrivate(object)); \
	if (thing) {\
		delete thing->nativeObj; \
		delete thing; \
		JSObjectSetPrivate(object, NULL);\
	}\
}

#define JSC_DESTRUCTOR_KEEP_WRAPPED(type) \
static void jsDestructor(JSObjectRef object) { \
type* thing = static_cast<type*>(JSObjectGetPrivate(object)); \
delete thing; \
}

namespace Arabica {
namespace DOM {

class JSCDOM {
public:
	JSCDOM();
	virtual ~JSCDOM();
	uscxml::Storage* storage;
	Arabica::XPath::XPath<std::string>* xpath;
};

}
}

#endif /* end of include guard: JSCDOM_H_1RC5LCG8 */
