#define protected public
#include "uscxml/Interpreter.h"
#include "uscxml/util/String.h"
#undef protected
#include <iostream>

int main(int argc, char** argv) {
	try {
		using namespace uscxml;
		using namespace Arabica::DOM;
		using namespace Arabica::XPath;

		const char* xml =
		    "<scxml>"
		    "  <state id=\"atomic\" />"
		    "  <state id=\"compound\">"
		    "    <state id=\"compoundChild1\" />"
		    "    <state id=\"compoundChild2\" />"
		    "  </state>"
		    "  <parallel id=\"parallel\">"
		    "  </parallel>"
		    "</scxml>";

		Interpreter interpreter = Interpreter::fromXML(xml, "");
		assert(interpreter);
		interpreter.getImpl()->init();

		Element<std::string> atomicState = interpreter.getImpl()->getState("atomic");
		assert(InterpreterImpl::isAtomic(atomicState));
		assert(!InterpreterImpl::isParallel(atomicState));
		assert(!InterpreterImpl::isCompound(atomicState));

		Element<std::string> compoundState = interpreter.getImpl()->getState("compound");
		assert(!InterpreterImpl::isAtomic(compoundState));
		assert(!InterpreterImpl::isParallel(compoundState));
		assert(InterpreterImpl::isCompound(compoundState));

		Element<std::string> parallelState = interpreter.getImpl()->getState("parallel");
		assert(!InterpreterImpl::isAtomic(parallelState));
		assert(InterpreterImpl::isParallel(parallelState));
		assert(!InterpreterImpl::isCompound(parallelState)); // parallel states are not compound!

		NodeSet<std::string> initialState = interpreter.getImpl()->getInitialStates();
		assert(initialState[0] == atomicState);

		NodeSet<std::string> childs = interpreter.getImpl()->getChildStates(compoundState);
		Node<std::string> compoundChild1 = interpreter.getImpl()->getState("compoundChild1");
		Node<std::string> compoundChild2 = interpreter.getImpl()->getState("compoundChild2");
		assert(childs.size() > 0);
		assert(InterpreterImpl::isMember(compoundChild1, childs));
		assert(InterpreterImpl::isMember(compoundChild2, childs));
		assert(!InterpreterImpl::isMember(compoundState, childs));

		assert(InterpreterImpl::isDescendant(compoundChild1, compoundState));

		{
			std::string idrefs("id1");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 1);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
		}

		{
			std::string idrefs(" id1");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 1);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
		}

		{
			std::string idrefs(" id1 ");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 1);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
		}

		{
			std::string idrefs(" \tid1\n ");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 1);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
		}

		{
			std::string idrefs("id1 id2 id3");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 3);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id2") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id3") == 0);
		}

		{
			std::string idrefs("\t  id1 \nid2\n\n id3\t");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 3);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id2") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id3") == 0);
		}

		{
			std::string idrefs("id1 \nid2  \tid3");
			std::list<std::string> tokenizedIdrefs = tokenize(idrefs);
			assert(tokenizedIdrefs.size() == 3);
			assert(tokenizedIdrefs.front().compare("id1") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id2") == 0);
			tokenizedIdrefs.pop_front();
			assert(tokenizedIdrefs.front().compare("id3") == 0);
		}

		std::string transEvents;
		transEvents = "error";
		assert(nameMatch(transEvents, "error"));
		assert(!nameMatch(transEvents, "foo"));

		transEvents = " error foo";
		assert(nameMatch(transEvents, "error"));
		assert(nameMatch(transEvents, "error.send"));
		assert(nameMatch(transEvents, "error.send.failed"));
		assert(nameMatch(transEvents, "foo"));
		assert(nameMatch(transEvents, "foo.bar"));
		assert(!nameMatch(transEvents, "errors.my.custom"));
		assert(!nameMatch(transEvents, "errorhandler.mistake"));
		// is the event name case sensitive?
		//	assert(!nameMatch(transEvents, "errOr.send"));
		assert(!nameMatch(transEvents, "foobar"));
	} catch(std::exception e) {
		std::cout << e.what();
		return false;
	} catch(uscxml::Event e) {
		std::cout << e;
		return false;
	}
}