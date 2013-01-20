#include "V8CharacterData.h"
#include "V8Comment.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Comment::Tmpl;

bool V8Comment::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
