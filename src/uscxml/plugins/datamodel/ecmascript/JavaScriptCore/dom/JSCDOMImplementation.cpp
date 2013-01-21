#include "JSCDOMImplementation.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCDOMImplementation::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCDOMImplementation::staticFunctions[] = {
	{ "hasFeature", hasFeatureCallback, kJSPropertyAttributeDontDelete },
	{ "createDocumentType", createDocumentTypeCallback, kJSPropertyAttributeDontDelete },
	{ "createDocument", createDocumentCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

}
}
