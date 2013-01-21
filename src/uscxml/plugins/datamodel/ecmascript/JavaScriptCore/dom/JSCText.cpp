#include "JSCCharacterData.h"
#include "JSCText.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCText::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCText::staticFunctions[] = {
	{ "splitText", splitTextCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

}
}
