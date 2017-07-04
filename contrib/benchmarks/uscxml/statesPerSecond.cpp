#include <iostream>
#include <chrono>
#include <stdlib.h>

#include "uscxml/uscxml.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/util/DOM.h"

using namespace std;
using namespace uscxml;
using namespace std::chrono;

long iterations = 0;
long initMs = 0;
system_clock::time_point now;
system_clock::time_point report;
system_clock::time_point endTime;

class PerfMon : public InterpreterMonitor {
	public: 
	virtual void beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
		if (HAS_ATTR(state, X("id")) && ATTR(state, X("id")) == "mark") {
			iterations++;
			now = system_clock::now();
			if (now > report) {
				report = now + seconds(1);
				std::cout << initMs << ", " << iterations << std::endl;
				iterations = 0;
			}
		}
		if (now > endTime) {
			::exit(EXIT_SUCCESS);
		}
	}
};

int main(int argc, char *argv[])
{
	system_clock::time_point start = system_clock::now();

	Interpreter sc = Interpreter::fromURL(argv[1]);
	ActionLanguage al;
	if (argc > 2) {
		if (std::string(argv[2]) == "large") {
	    al.microStepper = Factory::getInstance()->createMicroStepper("large", (MicroStepCallbacks*)sc);
		} else {
  	  al.microStepper = Factory::getInstance()->createMicroStepper("fast", (MicroStepCallbacks*)sc);
		}
  }
	sc.setActionLanguage(al);

	InterpreterState state = sc.step(); // initialize?

	PerfMon mon;
	sc.addMonitor(&mon);

	now = system_clock::now();
	initMs = duration_cast<milliseconds>(now - start).count();

	start = now;
	report = start + seconds(1);
	endTime = start + seconds(10);

	while(true) {
		sc.step();
	}

	return 0;
}
