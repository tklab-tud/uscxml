#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/concurrency/Timer.h"
#include "uscxml/concurrency/tinythread.h"

#include <iostream>

using namespace uscxml;

Timer t1;

bool testTimers() {
	{
		Measurement m(&t1);
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(1000));
	}
	std::cout << t1.elapsed << std::endl;
	return true;
}

int main(int argc, char** argv) {
	testTimers();
	return 0;
}