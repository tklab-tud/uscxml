/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

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
	uscxml::NameSpaceInfo* nsInfo;
	Arabica::XPath::XPath<std::string>* xpath;

};

}
}

#endif /* end of include guard: JSCDOM_H_1RC5LCG8 */
