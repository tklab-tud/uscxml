#include "uscxml/config.h"
#include "uscxml/Message.h"
#include "uscxml/concurrency/tinythread.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"

using namespace uscxml;
using namespace boost;

class Watcher : public DirectoryWatchMonitor {
	void handleChanges(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat) {
		std::cout << "Monitor on " << dir << ": " << action << " for " << file << std::endl;
	}
};

int main(int argc, char** argv) {

	Watcher watcher;
	DirectoryWatch* dw = new DirectoryWatch("/Users/sradomski/Desktop/tmp", true);
	dw->addMonitor(&watcher);
	while(true) {
		dw->updateEntries();
	}
}