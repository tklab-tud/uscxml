#define protected public
#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/transform/FSMToPromela.h"

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

extern int promela_debug;

void testInlinePromela() {
	{
		std::string test = "\
		#promela-inline:\n \
		This is foo!\
		";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 1 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_CODE);
		assert(boost::trim_copy(prmInls.inlines.front().content) == "This is foo!");
	}

	{
		std::string test = "#promela-progress";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 1);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_PROGRESS_LABEL);
	}

	{
		std::string test = "#promela-accept and then some";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 1 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_ACCEPT_LABEL);
	}

	{
		std::string test = "#promela-end and then some";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 1 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_END_LABEL);
	}

	{
		std::string test = "\
		#promela-event-source:\n \
		This is foo!\
		";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 1 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_EVENT_SOURCE);
		assert(prmInls.inlines.front().sequences.size() == 1);
		std::list<std::list<std::string> >::iterator seqsIter = prmInls.inlines.front().sequences.begin();
		std::list<std::string>::iterator seqIter = seqsIter->begin();
		assert(*seqIter++ == "This");
		assert(*seqIter++ == "is");
		assert(*seqIter++ == "foo!");
		assert(seqIter == seqsIter->end());
		seqsIter++;
		assert(seqsIter == prmInls.inlines.front().sequences.end());
	}

	{
		std::string test = "\
		#promela-event-source:\n \
		This is foo!\n \
		This is bar!\n \
		";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 0 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 1 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_EVENT_SOURCE);
		assert(prmInls.inlines.front().sequences.size() == 2);
		std::list<std::list<std::string> >::iterator seqsIter = prmInls.inlines.front().sequences.begin();
		std::list<std::string>::iterator seqIter = seqsIter->begin();
		assert(*seqIter++ == "This");
		assert(*seqIter++ == "is");
		assert(*seqIter++ == "foo!");
		assert(seqIter == seqsIter->end());
		seqsIter++;
		seqIter = seqsIter->begin();
		assert(*seqIter++ == "This");
		assert(*seqIter++ == "is");
		assert(*seqIter++ == "bar!");
		assert(seqIter == seqsIter->end());
		seqsIter++;
		assert(seqsIter == prmInls.inlines.front().sequences.end());
	}

	{
		std::string test = "\
		#promela-event-source-custom:\n \
		This is foo!\
		";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 1 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 0);
		assert(prmInls.inlines.size() == 1);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM);
		assert(prmInls.inlines.front().sequences.size() == 0);
		assert(boost::trim_copy(prmInls.inlines.front().content) == "This is foo!");
	}

	{
		std::string test = "\
		#promela-event-source-custom:\n \
		This is foo! \n\
		#promela-progress\
		";
		PromelaInlines prmInls = FSMToPromela::getInlinePromela(test);
		assert(prmInls.acceptLabels == 0 &&
		       prmInls.codes == 0 &&
		       prmInls.customEventSources == 1 &&
		       prmInls.endLabels == 0 &&
		       prmInls.eventSources == 0 &&
		       prmInls.progressLabels == 1);
		assert(prmInls.inlines.size() == 2);
		assert(prmInls.inlines.front().type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM);
		assert(prmInls.inlines.front().sequences.size() == 0);
		assert(boost::trim_copy(prmInls.inlines.front().content) == "This is foo!");
	}
}

void testPromelaParser() {

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
	expressions.push_back("typedef D { short f; byte  g }; ");
	expressions.push_back("x = 1");
	expressions.push_back("x = foo.bar[2].baz; ");
	expressions.push_back("_event.data[1].aParam.key1.key2[1].key3.key4");
	expressions.push_back("_event.data.aParam");
	expressions.push_back("_event.data");
	expressions.push_back("_event");
	expressions.push_back("states");
	expressions.push_back("states[1]");
	expressions.push_back("_x.states[1]");
	expressions.push_back("_x.states[1].foo");
	expressions.push_back("_event.data[1].aParam.key1.key2[1].key3.key4");

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
	expressions.push_back("printf(\"result %d: %d\\n\", id, res, foo, bar)");
	expressions.push_back("printf(\"x = %d\\n\", x)");
	expressions.push_back("(n <= 1)");
	expressions.push_back("res = (a*a+b)/2*a;");
	expressions.push_back("assert(0)	/* a forced stop, (Chapter 6) */");
	expressions.push_back("assert(count == 0 || count == 1)");
	expressions.push_back("busy[4 - 3] = 1;");

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

int main(int argc, char** argv) {
	testInlinePromela();
	testPromelaParser();
}