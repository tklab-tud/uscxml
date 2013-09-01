#include "V8EntityReference.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8EntityReference::Tmpl;
bool V8EntityReference::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
