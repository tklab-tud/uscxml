#define protected public
#include "uscxml/util/URL.h"
#include "uscxml/Interpreter.h"
#include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/Predicates.h"

#include <xercesc/util/PlatformUtils.hpp>
#include <xercesc/dom/DOM.hpp>

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace XERCESC_NS;

extern int promela_debug;

void testInlinePromela() {


	DOMImplementation *implementation = DOMImplementationRegistry::getDOMImplementation(X("LS"));
	DOMDocument* document = implementation->createDocument();

	{
		std::string test = "\
		promela-code This is foo!\
		";

		DOMComment* comment = document->createComment(X(test));
		PromelaInline inl(comment);
		assert(inl.type == PromelaInline::PROMELA_CODE);
		assert(inl.content == "This is foo!");
	}

	{
		std::string test = "\
		promela-code\n \
		This is foo!\
		";

		DOMComment* comment = document->createComment(X(test));
		PromelaInline inl(comment);
		assert(inl.type == PromelaInline::PROMELA_CODE);
		assert(inl.content == "This is foo!");
	}

	{
		std::string test = "\
		promela-event\n \
		[{\"name\": \"e1\", \"data\": { \"foo\": \"some string\" }}, \
     {\"name\": \"e1\", \"data\": { \"bar\": 12 }}]";

		DOMComment* comment = document->createComment(X(test));
		PromelaInline inl(comment);
		assert(inl.type == PromelaInline::PROMELA_EVENT_ONLY);

		PromelaEventSource es(inl);
		assert(es.events.array.size() == 2);

	}

#if 0
	{
		Interpreter interpreter = Interpreter::fromURL("/Users/sradomski/Documents/TK/Code/uscxml/test/uscxml/promela/test-event-source-auto.scxml");
		assert(interpreter);
		PromelaInlines inls(interpreter.getImpl()->getDocument()->getDocumentElement());

		assert(inls.getAllOfType(PromelaInline::PROMELA_EVENT_ONLY).size() == 2);
		assert(inls.getAllOfType(PromelaInline::PROMELA_EVENT_ALL_BUT).size() == 1);
	}
#endif
#if 0
	{
		std::string test = "\
		#promela-inline:\n \
		This is foo!\
		";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 1 &&
		       prmInls.nrEventSources == 0 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_CODE);
		assert(boost::trim_copy(prmInls.code.front().content) == "This is foo!");
	}

	{
		std::string test = "#promela-progress";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 0 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 1);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_PROGRESS_LABEL);
	}

	{
		std::string test = "#promela-accept and then some";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 1 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 0 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_ACCEPT_LABEL);
	}

	{
		std::string test = "#promela-end and then some";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 0 &&
		       prmInls.nrEndLabels == 1 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_END_LABEL);
	}

	{
		std::string test = "\
		#promela-event-source:\n \
		This is foo!\
		";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 1 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_EVENT_SOURCE);

		PromelaEventSource pmlES(prmInls.code.front());
		assert(pmlES.sequences.size() == 1);
		std::list<std::list<std::string> >::iterator seqsIter = pmlES.sequences.begin();
		std::list<std::string>::iterator seqIter = seqsIter->begin();
		assert(*seqIter++ == "This");
		assert(*seqIter++ == "is");
		assert(*seqIter++ == "foo!");
		assert(seqIter == seqsIter->end());
		seqsIter++;
		assert(seqsIter == pmlES.sequences.end());
	}

	{
		std::string test = "\
		#promela-event-source:\n \
		This is foo!\n \
		This is bar!\n \
		";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 1 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_EVENT_SOURCE);

		PromelaEventSource pmlES(prmInls.code.front());

		assert(pmlES.sequences.size() == 2);
		std::list<std::list<std::string> >::iterator seqsIter = pmlES.sequences.begin();
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
		assert(seqsIter == pmlES.sequences.end());
	}

	{
		std::string test = "\
		#promela-event-source-custom:\n \
		This is foo!\
		";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 1 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 0);
		assert(prmInls.code.size() == 1);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM);

		PromelaEventSource pmlES(prmInls.code.front());

		assert(pmlES.sequences.size() == 0);
		assert(boost::trim_copy(pmlES.source.content) == "This is foo!");
	}

	{
		std::string test = "\
		#promela-event-source-custom:\n \
		This is foo! \n\
		#promela-progress\
		";
		PromelaInlines prmInls = PromelaInlines::fromString(test);
		assert(prmInls.nrAcceptLabels == 0 &&
		       prmInls.nrCodes == 0 &&
		       prmInls.nrEventSources == 1 &&
		       prmInls.nrEndLabels == 0 &&
		       prmInls.nrProgressLabels == 1);
		assert(prmInls.code.size() == 2);
		assert(prmInls.code.front().type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM);

		PromelaEventSource pmlES(prmInls.code.front());

		assert(pmlES.sequences.size() == 0);
		assert(boost::trim_copy(pmlES.source.content) == "This is foo!");
	}
#endif
}

void checkTokenLocations(const std::string& expr, PromelaParserNode* ast) {
	if (ast->loc != NULL) {
		assert(expr.substr(ast->loc->firstCol, ast->loc->lastCol - ast->loc->firstCol) == ast->value);
	}
	for (std::list<PromelaParserNode*>::iterator opIter = ast->operands.begin(); opIter != ast->operands.end(); opIter++) {
		checkTokenLocations(expr, *opIter);
	}
}

void testPromelaParser() {

	promela_debug = 0;
#if 1
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
	expressions.push_back("\n\n\n\n    int foo = 3;\n\nint bar = 5;");


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
			if (!boost::contains(*exprIter, "\n"))
				checkTokenLocations(*exprIter, ast.ast);
		} catch (Event e) {
			std::cerr << e << std::endl;
		}
	}
#endif

	{
		try {
			PromelaParser ast("\"foo");
			assert(false);
		} catch(...) {
		}
	}
}

int main(int argc, char** argv) {
	try {
		::XERCESC_NS::XMLPlatformUtils::Initialize();
	} catch (const XERCESC_NS::XMLException& toCatch) {
		ERROR_PLATFORM_THROW("Cannot initialize XercesC: " + X(toCatch.getMessage()).str());
	}

	testInlinePromela();
	testPromelaParser();
}
