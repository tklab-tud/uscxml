#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <sys/time.h>

#include <iostream>

using namespace uscxml;
using namespace std::chrono;

int main(int argc, char** argv) {
	if (argc < 2) {
		std::cout << "Expected filename as first parameter" << std::endl;
		exit(EXIT_FAILURE);
	}

	Interpreter interpreter = Interpreter::fromURL(argv[1]);

	InterpreterState state;
	system_clock::time_point start = system_clock::now();

	while((state = interpreter.step()) != InterpreterState::USCXML_INITIALIZED) {}
	system_clock::time_point now = system_clock::now();

	std::cout << "init: " << duration_cast<milliseconds>(now - start).count() << "ms" << std::endl;

	start = system_clock::now();
	system_clock::time_point endTime = start + seconds(10);
	system_clock::time_point report = start + seconds(1);

	unsigned long iterations = 0;

	while(true) {
		now = system_clock::now();
		if (now > endTime)
			break;

		interpreter.step();

		iterations++;
		if (now > report) {
			report = now + seconds(1);
			std::cout << "steps / sec: " << iterations << std::endl;
			iterations = 0;
		}
	}
}
