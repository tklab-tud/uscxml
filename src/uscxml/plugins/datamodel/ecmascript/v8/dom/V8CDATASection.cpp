#include "V8CDATASection.h"
#include "V8Text.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8CDATASection::Tmpl;

bool V8CDATASection::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
