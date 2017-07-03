#include <iostream>
#include <chrono>
#include <stdlib.h>

#include "test.h"

using namespace std;
using namespace std::chrono;

typedef MACHINE_NAME sc;

long iterations = 0;
long initMs = 0;
system_clock::time_point report;
system_clock::time_point endTime;

template<> void sc::state_actions<sc::state_mark>::enter(sc::data_model &m)
{
	iterations++;
	system_clock::time_point now = system_clock::now();

	if (now > report) {
		report = now + seconds(1);
		std::cout << initMs << ", " << iterations << std::endl;
		iterations = 0;
	}
	if (now > endTime) {
		::exit(EXIT_SUCCESS);
	}
}

int main(int argc, char *argv[])
{
	system_clock::time_point start = system_clock::now();

	sc sc0;
	system_clock::time_point now = system_clock::now();

	initMs = duration_cast<milliseconds>(now - start).count();

	start = now;
	report = start + seconds(1);
	endTime = start + seconds(10);

	sc0.init();
	return 0;
}
