/* 
 * we will have to manage these by hand 
 */

%ignore uscxml::Event::data; // too ambituous
%ignore uscxml::Event::namelist; // not needed
%ignore uscxml::Event::params; // not needed
%ignore uscxml::Event::uuid; // only for internal use

%ignore uscxml::Event::hideSendId; // not needed
%ignore uscxml::Event::sendid; // supposed to be undef not empty string
%ignore uscxml::Event::invokeid; // supposed to be undef not empty string

%ignore uscxml::Event::eventtype; // not an enum but a string
%ignore uscxml::Event::origin; // supposed to be undef not empty string
%ignore uscxml::Event::origintype; // supposed to be undef not empty string

%{
using uscxml::Data;
%}

%include "uscxml/messages/Event.h"
