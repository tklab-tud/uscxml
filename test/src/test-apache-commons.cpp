#include "uscxml/Interpreter.h"
#include <glog/logging.h>

using namespace uscxml;
using namespace Arabica::DOM;
using namespace Arabica::XPath;

static std::string path;

bool testEvents1() {
	LOG(INFO) << "---- testEvent1 ";
	Interpreter* interpreter = Interpreter::fromURI(path + "/eventdata-01.xml");
	interpreter->start();
	interpreter->waitForStabilization();
	assert(interpreter->getConfiguration().size() == 1);
	assert(Interpreter::isMember(interpreter->getState("state1"), interpreter->getConfiguration()));

	Event eventFoo;
	eventFoo.name = "event.foo";
	eventFoo.atom = "3";
	interpreter->receive(eventFoo);
	interpreter->waitForStabilization();
	assert(interpreter->getConfiguration().size() == 1);
	assert(Interpreter::isMember(interpreter->getState("state3"), interpreter->getConfiguration()));

	Event eventBar;
	eventBar.name = "event.bar";
	eventBar.atom = "6";
	interpreter->receive(eventBar);
	interpreter->waitForStabilization();
	assert(interpreter->getConfiguration().size() == 1);
	assert(Interpreter::isMember(interpreter->getState("state6"), interpreter->getConfiguration()));

	Event eventBaz;
	eventBaz.name = "event.baz";
	eventBaz.atom = "7";
	interpreter->receive(eventBaz);

	delete interpreter;
	return true;
}

bool testEvents2() {
	LOG(INFO) << "---- testEvent2 ";
	Interpreter* interpreter = Interpreter::fromURI(path + "/eventdata-02.xml");
	interpreter->start();
	interpreter->waitForStabilization();
	assert(interpreter->getConfiguration().size() == 1);
	assert(Interpreter::isMember(interpreter->getState("state0"), interpreter->getConfiguration()));

	Event eventConnAlert;
	eventConnAlert.name = "connection.alerting";
	eventConnAlert.atom = "'line2'";
	interpreter->receive(eventConnAlert);
	interpreter->waitForStabilization();
	assert(interpreter->getConfiguration().size() == 1);
	assert(Interpreter::isMember(interpreter->getState("state2"), interpreter->getConfiguration()));

	Event eventConnAlert2;
	eventConnAlert2.name = "connection.alerting";
	eventConnAlert2.compound["line"] = Data(std::string("4"));
	interpreter->receive(eventConnAlert2);

	delete interpreter;
	return true;
}

//bool testEvents3() {
//  LOG(INFO) << "---- testEvent3 ";
//  Interpreter* Interpreter = new Interpreter(path + "/eventdata-03.xml");
//  interpreter->start();
//  interpreter->waitForStabilization();
//  Thread::sleepMs(200);
//  assert(interpreter->getConfiguration().size() == 1);
//  assert(Interpreter::isMember(interpreter->getState("state0"), interpreter->getConfiguration()));
//
//  Event eventConnAlert;
//  eventConnAlert.name = "connection.alerting";
//  eventConnAlert.atom = "'line2'";
//  interpreter->receive(eventConnAlert);
//  Thread::sleepMs(200);
//  assert(interpreter->getConfiguration().size() == 1);
//  assert(Interpreter::isMember(interpreter->getState("state2"), interpreter->getConfiguration()));
//
//  Event eventConnAlert2;
//  eventConnAlert2.name = "connection.alerting";
//  eventConnAlert2.compound["line"] = Data(std::string("4"));
//  interpreter->receive(eventConnAlert2);
//  Thread::sleepMs(200);
//  assert(interpreter->getConfiguration().size() == 1);
//  assert(Interpreter::isMember(interpreter->getState("state4"), interpreter->getConfiguration()));
//
//  delete Interpreter;
//  return true;
//}


int main(int argc, char** argv) {
	if (argc != 2) {
		std::cerr << "Expected path to scxml file from apache commons distribution" << std::endl;
		exit(EXIT_FAILURE);
	}

	path = "file://";
	path += argv[1];

	if (!testEvents1())
		return EXIT_FAILURE;
	if (!testEvents2())
		return EXIT_FAILURE;
//  if (!testEvents3())
//    return EXIT_FAILURE;

//
//  Interpreter* scxmlInterpreter = new Interpreter(path + "/tie-breaker-01.xml");
//  SCXMLRunner* scxmlRun = new SCXMLRunner(scxmlInterpreter);
//  scxmlRun->start();
//
//  Thread::sleepMs(100);
//  assert(Interpreter::isMember(scxmlinterpreter->getState("ten"), scxmlinterpreter->getConfiguration()));
//
//  boost::shared_ptr<Event> event = boost::shared_ptr<Event>(new Event());
//  event->name = "ten.done";
//  scxmlinterpreter->receive(event);
//  scxmlRun->join();
//  scxmlinterpreter->receive(event);

}