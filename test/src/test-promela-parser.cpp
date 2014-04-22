#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

extern int promela_debug;

int main(int argc, char** argv) {
	promela_debug = 0;

	std::list<std::string> expressions;
	/* declarations  */
	expressions.push_back("bool b1");
	expressions.push_back("bool b1;");
	expressions.push_back("bool b1, b2, b3");
	expressions.push_back("bool b1, b2, b3;");
	expressions.push_back("bool b1, b2 = 3 + 4, b3, b4, b5;");
	expressions.push_back("bool b1; bool b2; bool b3; bool b4;");
	expressions.push_back("bool b1; bool b2; bool b3, b4, b5;");
	expressions.push_back("bit b = 1;");
	expressions.push_back("byte state = 1;");
	expressions.push_back("bool b1, b2 = 1, b3;");
	expressions.push_back("bool busy[3];");
	expressions.push_back("bool busy[3], us[4];");
	expressions.push_back("mtype = {\nred, white, blue,\nabort, accept, ack, sync_ack, close, connect,\ncreate, data, eof, open, reject, sync, transfer,\nFATAL, NON_FATAL, COMPLETE\n}");

	/* expressions  */
	expressions.push_back("i+1");
	expressions.push_back("(x == false || t == Bturn);");
	expressions.push_back("a + (1 << b)");
	expressions.push_back("(a + 1) << b");
	expressions.push_back("(b < N)");
	expressions.push_back("(mt+1)%MAX;");
	expressions.push_back("state[0] = state[3] + 5 * state[3*2/n]");

	/* statements  */
	expressions.push_back("t = Bturn;");
	expressions.push_back("c++");
	expressions.push_back("state = state - 1");
	expressions.push_back("printf(\"hello world\\n\")");
	expressions.push_back("printf(\"result %d: %d\n\", id, res, foo, bar)");
	expressions.push_back("printf(\"x = %d\n\", x)");
	expressions.push_back("(n <= 1)");
	expressions.push_back("res = (a*a+b)/2*a;");
	expressions.push_back("assert(0)	/* a forced stop, (Chapter 6) */");
	expressions.push_back("assert(count == 0 || count == 1)");
	expressions.push_back("busy[4 - 3] = 1;");

	while(true)
		for (std::list<std::string>::iterator exprIter = expressions.begin();
		        exprIter != expressions.end();
		        exprIter++) {
			try {
				std::cout << std::endl << "'" << *exprIter << "':" << std::endl;
				PromelaParser ast(*exprIter);
				ast.dump();
			} catch (Event e) {
				std::cerr << e << std::endl;
			}
		}
}