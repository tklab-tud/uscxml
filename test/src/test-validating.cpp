#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/debug/InterpreterIssue.h"
#include "uscxml/interpreter/Logging.h"
#include <xercesc/util/PlatformUtils.hpp>

using namespace uscxml;

std::set<std::string> issueLocationsForXML(const std::string xml) {
	Interpreter interpreter = Interpreter::fromXML(xml, "");

	// common xmlns and version requirement on scxml attribute
	interpreter.getImpl()->getDocument()->getDocumentElement()->setAttribute(X("xmlns"), X("http://www.w3.org/2005/07/scxml"));
	interpreter.getImpl()->getDocument()->getDocumentElement()->setAttribute(X("version"), X("1.0"));

	std::list<InterpreterIssue> issues = interpreter.validate();

	std::set<std::string> issueLocations;

	for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
		std::cout << *issueIter << std::endl;
		issueLocations.insert(issueIter->xPath);
	}
	return issueLocations;
}

size_t runtimeIssues;
class IssueMonitor : public InterpreterMonitor {
public:
	IssueMonitor() {
		runtimeIssues = 0;
	}
	void reportIssue(Interpreter& intrpreter, const InterpreterIssue& issue) {
		runtimeIssues++;
	}
};

int main(int argc, char** argv) {

	using namespace XERCESC_NS;

	int iterations = 1;

	while(iterations--) {

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Potential endless loop

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<datamodel><data id=\"counter\" expr=\"5\" /></datamodel>"
			    "	<state id=\"foo\">"
			    "		<onentry><script>counter--;</script></onentry>"
			    "		<transition target=\"foo\" cond=\"counter > 0\" />"
			    "		<transition target=\"bar\" cond=\"counter == 0\" />"
			    " </state>"
			    "	<state id=\"bar\" final=\"true\" />"
			    "</scxml>";

			IssueMonitor monitor;
			Interpreter interpreter = Interpreter::fromXML(xml, "");
			interpreter.addMonitor(&monitor);

			while(interpreter.step() > 0) {}

			// four identical configurations between macrosteps
			assert(runtimeIssues == 4);
		}

		if (1) {
			// Unreachable states 1

			const char* xml =
			    "<scxml>"
			    "	<state id=\"foo\">"
			    "		<parallel id=\"foz\">"
			    "			<state id=\"s0\" />"
			    "			<state id=\"s1\" />"
			    "			<state id=\"s2\" />"
			    "		</parallel>"
			    " </state>"
			    "	<state id=\"bar\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"bar\"]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Invalid parents
			const char* xml =
			    "<scxml>"
			    "		<onentry>"
			    "			<cancel sendid=\"foo\" />"
			    "		</onentry>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("/scxml[1]/onentry[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// State has no 'id' attribute
			// *** This is not actually an error! ***
			const char* xml =
			    "<scxml>"
			    "	<state>"
			    "		<transition/>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("/scxml[1]/state[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Duplicate state with id
			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\" />"
			    " <state id=\"start\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Transition has non-existant target state

			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<transition target=\"done\" />"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Useless history 1

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"bar\">"
			    "   <history id=\"bar\" />"
			    "   <state id=\"baz\" />"
			    "   <transition event=\"e.foo\" target=\"done\" />"
			    "   <transition event=\"e.bar\" target=\"baz\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//history[@id=\"bar\"]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Useless history 2

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"bar\">"
			    "   <history id=\"bar\">"
			    "       <transition target=\"foo\" />"
			    "   </history>"
			    "   <transition target=\"done\" />"
			    "	<state id=\"foo\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//history[@id=\"bar\"]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// No legal completion

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"foo bar\">"
			    "	<state id=\"foo\" />"
			    "	<state id=\"bar\" />"
			    "   <transition target=\"foo bar\" />"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 2);
		}

		if (1) {
			// attribute constraints

			{
				// initial attribute and <initial> child
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\" initial=\"foo\">"
				    "   <initial>"
				    "       <transition target=\"foo\" />"
				    "   </initial>"
				    "	<state id=\"foo\" />"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// initial attribute with atomic state
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\" initial=\"\" />"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// initial child with atomic state
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "   <initial>"
				    "       <transition target=\"start\" />"
				    "   </initial>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
				assert(issueLocations.size() == 2); // also invalid non-child target state in initial
			}

			// combinations of namelist, content and param
			{
				// send with content and namelist, not allowed
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "   <onentry>"
				    "     <send target=\"#_external\" namelist=\"var1\">"
				    "       <content>Foo!</content>"
				    "     </send>"
				    "   </onentry>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[1]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// send with content and params, not allowed
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "   <onentry>"
				    "     <send target=\"#_external\">"
				    "       <param name=\"foo\" expr=\"3\" />"
				    "       <content>Foo!</content>"
				    "     </send>"
				    "   </onentry>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[1]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// send with params and namelist, perfectly acceptable
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "   <onentry>"
				    "     <send target=\"#_external\" namelist=\"foo\">"
				    "       <param name=\"foo\" expr=\"3\" />"
				    "     </send>"
				    "   </onentry>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.size() == 0);
			}

			{
				// invoke with content and src, not allowed
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "     <invoke type=\"scxml\" src=\"var1\">"
				    "       <content>Foo!</content>"
				    "     </invoke>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]/invoke[1]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// invoke with namelist and param, not allowed
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "     <invoke type=\"scxml\" namelist=\"var1\">"
				    "       <param name=\"foo\" expr=\"3\" />"
				    "     </invoke>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]/invoke[1]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}

			{
				// invoke with param and content, perfectly acceptable
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "     <invoke type=\"scxml\">"
				    "       <param name=\"foo\" expr=\"3\" />"
				    "       <content>Foo!</content>"
				    "     </invoke>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.size() == 0);
			}

			{
				// invoke with namelist and content, perfectly acceptable
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "     <invoke type=\"scxml\" namelist=\"var1\">"
				    "       <content>Foo!</content>"
				    "     </invoke>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.size() == 0);
			}

			{
				// donedata with content and param, not allowed
				const char* xml =
				    "<scxml>"
				    " <state id=\"start\">"
				    "     <donedata>"
				    "       <param name=\"foo\" expr=\"3\" />"
				    "       <content>Foo!</content>"
				    "     </donedata>"
				    " </state>"
				    "</scxml>";

				std::set<std::string> issueLocations = issueLocationsForXML(xml);
				assert(issueLocations.find("//state[@id=\"start\"]/donedata[1]") != issueLocations.end());
				assert(issueLocations.size() == 1);
			}


		}

		if (1) {
			// Transition can never be optimally enabled (conditionless, eventless)

			const char* xml =
			    "<scxml>"
			    "  <state id=\"start\">"
			    "    <transition target=\"done\" />"
			    "    <transition target=\"done\" />"
			    "  </state>"
			    "  <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/transition[2]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}
		if (1) {
			// Transition can never be optimally enabled (conditionless, more events)

			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<transition event=\"error\" target=\"done\" />"
			    "		<transition event=\"error.bar error.foo\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/transition[2]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}


		if (1) {
			// Initial attribute has invalid target state

			const char* xml =
			    "<scxml initial=\"foo\">"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("/scxml[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Initial attribute with target outside of children

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"foo done\">"
			    "	<state id=\"foo\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}
		if (1) {
			// Initial transition with target outside of children

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial>"
			    "       <transition target=\"foo done\" />"
			    "   </initial>"
			    "	<state id=\"foo\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1); // there are actually two issues with the transition
		}
		if (1) {
			// Initial history transition with target outside of children

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"bar\">"
			    "   <history id=\"bar\">"
			    "       <transition target=\"foo done\" />"
			    "   </history>"
			    "	<state id=\"foo\">"
			    "       <transition target=\"baz\" />"
			    "   </state>"
			    "	<state id=\"baz\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//history[@id=\"bar\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}
		if (1) {
			// Initial transition with target outside of children

			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial>"
			    "       <transition target=\"foo done\" />"
			    "   </initial>"
			    "	<state id=\"foo\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Initial transition with event
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial>"
			    "       <transition event=\"e.foo\" target=\"foo\" />"
			    "   </initial>"
			    "	<state id=\"foo\" />"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Initial transition with condition
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial>"
			    "       <transition cond=\"true\" target=\"foo\" />"
			    "   </initial>"
			    "	<state id=\"foo\" />"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Initial with multiple transitions
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial>"
			    "       <transition target=\"foo\" />"
			    "       <transition target=\"foo\" />"
			    "   </initial>"
			    "	<state id=\"foo\" />"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Initial with no transitions
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\">"
			    "   <initial />"
			    "	<state id=\"foo\" />"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"foo\"]") != issueLocations.end()); // unreachable
			assert(issueLocations.find("//state[@id=\"start\"]/initial[1]") != issueLocations.end());
			assert(issueLocations.size() == 2);
		}

		if (1) {
			// History transition with event
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"bar\">"
			    "   <history id=\"bar\">"
			    "       <transition event=\"e.foo\" target=\"foo\" />"
			    "   </history>"
			    "	<state id=\"foo\">"
			    "       <state id=\"foo.s1\">"
			    "           <transition target=\"foo.s2\" />"
			    "       </state>"
			    "       <state id=\"foo.s2\" />"
			    "   </state>"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//history[@id=\"bar\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// History transition with condition
			const char* xml =
			    "<scxml>"
			    " <state id=\"start\" initial=\"bar\">"
			    "   <history id=\"bar\">"
			    "       <transition cond=\"false\" target=\"foo\" />"
			    "   </history>"
			    "	<state id=\"foo\">"
			    "       <state id=\"foo.s1\">"
			    "           <transition target=\"foo.s2\" />"
			    "       </state>"
			    "       <state id=\"foo.s2\" />"
			    "   </state>"
			    "   <transition event=\"e.bar\" target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//history[@id=\"bar\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Send to unknown IO Processor

			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<send type=\"non-existant\" />"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// SCXML document requires unknown datamodel

			const char* xml =
			    "<scxml datamodel=\"non-existant\">"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("/scxml[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (1) {
			// Unknown executable content element

			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<nonexistant />"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/nonexistant[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error in script

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<script>"
			    "   $wfwegr^ "
			    " </script>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("/scxml[1]/script[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error in cond attribute

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<if cond=\"%2345\">"
			    "			<elseif cond=\"%2345\" />"
			    "			</if>"
			    "		</onentry>"
			    "		<transition cond=\"%2345\" />"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/transition[1]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/if[1]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/if[1]/elseif[1]") != issueLocations.end());
			assert(issueLocations.size() == 3);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error in expr attribute

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<datamodel>"
			    "		<data id=\"foo\" expr=\"%2345\" />"
			    "	</datamodel>"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<log expr=\"%2345\" />"
			    "			<assign location=\"foo\" expr=\"%2345\" />"
			    "			<send>"
			    "				<param expr=\"%2345\" />"
			    "			</send>"
			    "			<send>"
			    "				<content expr=\"%2345\" />"
			    "			</send>"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/log[1]") != issueLocations.end());
			assert(issueLocations.find("//data[@id=\"foo\"]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/assign[1]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[1]/param[1]") != issueLocations.end());
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[2]/content[1]") != issueLocations.end());
			assert(issueLocations.size() == 5);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error with foreach

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<foreach item=\"%2345\" index=\"%2345\" array=\"%2345\">"
			    "			</foreach>"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/foreach[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error with send

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<send eventexpr=\"%2345\" targetexpr=\"%2345\" typeexpr=\"%2345\" idlocation=\"%2345\" delayexpr=\"%2345\" />"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/send[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error with invoke

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<state id=\"start\">"
			    "		<invoke typeexpr=\"%2345\" srcexpr=\"%2345\" idlocation=\"%2345\" />"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/invoke[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

		if (Factory::getInstance()->hasDataModel("ecmascript")) {
			// Syntax error with cancel

			const char* xml =
			    "<scxml datamodel=\"ecmascript\">"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<cancel sendidexpr=\"%2345\" />"
			    "		</onentry>"
			    " </state>"
			    "</scxml>";

			std::set<std::string> issueLocations = issueLocationsForXML(xml);
			assert(issueLocations.find("//state[@id=\"start\"]/onentry[1]/cancel[1]") != issueLocations.end());
			assert(issueLocations.size() == 1);
		}

	}

	return EXIT_SUCCESS;
}
