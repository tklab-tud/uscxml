%module(directors="1", allprotected="1") uscxmlNativePHP

// import swig typemaps
//%include <arrays_java.i>
//%include <inttypes.i>
//%include <boost_shared_ptr.i>
%include <std_string.i>

// disable warning related to unknown base class
#pragma SWIG nowarn=401
//%ignore boost::enable_shared_from_this;

//%javaconst(1);

# %shared_ptr(uscxml::dom::Element);
# %shared_ptr(uscxml::dom::Executable);


//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Interpreter.h"

using namespace uscxml;

%}

%insert("begin") %{
void*** tsrm_ls;
%}

//%rename(toString) operator<<;


//***********************************************
// Parse the header file to generate wrappers
//***********************************************

%include "../../../uscxml/Message.h"
%include "../../../uscxml/Interpreter.h"

