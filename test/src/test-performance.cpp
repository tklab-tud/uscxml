#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/util/DOM.h"

#include <chrono>
#include <iostream>

using namespace uscxml;
using namespace std::chrono;

long iterations = 0;
long initMs = 0;
bool exitPerf = false;
system_clock::time_point now;
system_clock::time_point start;
system_clock::time_point report;
system_clock::time_point endTime;

class PerfMon : public InterpreterMonitor {
public:
	virtual void beforeEnteringState(const std::string& sessionId,
	                                 const std::string& stateName,
	                                 const XERCESC_NS::DOMElement* state) {
		if (stateName == "mark") {
			iterations++;
			now = system_clock::now();
			if (now > report) {
				report = now + seconds(1);
				std::cout << initMs << ", " << iterations << std::endl;
				iterations = 0;
			}
		}
		if (now > endTime) {
			exitPerf = true;
		}
	}
};

int main(int argc, char** argv) {
	if (argc < 2) {
		std::cout << "Expected filename as first parameter" << std::endl;
		exit(EXIT_FAILURE);
	}
	{
		start = system_clock::now();

		Interpreter sc = Interpreter::fromURL(argv[1]);
		sc.step(); // initialize?

		PerfMon mon;
		sc.addMonitor(&mon);

		now = system_clock::now();
		initMs = duration_cast<milliseconds>(now - start).count();

		start = now;
		report = start + seconds(1);
		endTime = start + seconds(10);

		while(true) {
			sc.step();
			if (exitPerf) {
				goto DONE_AND_EXIT;
			}
		}
	}
DONE_AND_EXIT:
	return 0;
}
