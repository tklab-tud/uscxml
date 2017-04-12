#define XERCES_HAS_CPP_NAMESPACE 1

%include <std_string.i>

/*

swig -I/Users/sradomski/Documents/TK/Code/uscxml2/build/cli/deps/xerces-c/include/ -javascript -jsc -c++ uscxml.i
gcc -I/Users/sradomski/Documents/TK/Code/uscxml2/build/cli/deps/xerces-c/include/ ./uscxml_wrap.cxx

*/

%module JSCDOM

%import "uscxml/config.h"
%import "uscxml/Common.h"

#ifndef NO_XERCESC
%import "xercesc/util/XercesDefs.hpp"
%import "xercesc/util/Xerces_autoconf_config.hpp"

%include "../../common/bindings/dom/ignore.i"
%include "../../common/bindings/dom/defines.i"
%include "../../common/bindings/dom/typemaps-general.i"

// in typemap
%typemap(in) XMLCh * %{
  $1 = JS2XMLString($input, context);
%}

%typemap(freearg) XMLCh * %{
  delete[] $1;
%}

// out typemap
%typemap(out) XMLCh * %{
  $result = XMLString2JS($1, context);
%}


%include "../../common/bindings/dom/dom.i"
#endif

// Operators we do want
// %rename(operator_assignment) operator=;
%rename(operator_equal_to) operator==;
%rename(operator_not_equal_to) operator!=;

%include "../../common/bindings/event.i"
