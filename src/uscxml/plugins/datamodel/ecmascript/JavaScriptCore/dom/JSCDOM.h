#ifndef JSCDOM_H_1RC5LCG8
#define JSCDOM_H_1RC5LCG8

#include "uscxml/Interpreter.h"
#include <JavaScriptCore/JavaScriptCore.h>

#define JSC_DESTRUCTOR(type) \
static void jsDestructor(JSObjectRef object) { \
type* thing = static_cast<type*>(JSObjectGetPrivate(object)); \
delete thing; \
}

namespace uscxml {

class JSCDOM {
public:
	JSCDOM();
	virtual ~JSCDOM() { };

  Interpreter* interpreter;
  Arabica::XPath::XPath<std::string>* xpath;
};

}


#endif /* end of include guard: JSCDOM_H_1RC5LCG8 */
