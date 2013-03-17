#include "uscxml/config.h"
#include "uscxml/Message.h"
#include "uscxml/concurrency/tinythread.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"

#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <dirent.h>
#include <string.h>
#include <iostream>

using namespace uscxml;
using namespace boost;

class Watcher : public DirectoryWatchMonitor {
	void handleChanges(DirectoryWatch::Action action, const std::string dir, const std::string file, struct stat fileStat) {
		std::cout << "Monitor on " << dir << ": " << action << " for " << file << std::endl;
	}
};

int main(int argc, char** argv) {

	int mDescriptor = kqueue();

	struct kevent filters[2];
	struct kevent event;

	struct timespec mTimeOut;
	mTimeOut.tv_sec = 20;
	mTimeOut.tv_nsec = 20000000;

	int fd1 = open("/Users/sradomski/Desktop/wrls", O_RDONLY);
	int fd2 = open("/Users/sradomski/Desktop/tmp", O_RDONLY);

	EV_SET(&filters[0], fd1, EVFILT_VNODE,
	       EV_ADD | EV_ENABLE | EV_ONESHOT,
	       NOTE_DELETE | NOTE_WRITE | NOTE_EXTEND | NOTE_ATTRIB | NOTE_LINK | NOTE_RENAME | NOTE_REVOKE,
	       0, NULL);
	EV_SET(&filters[1], fd2, EVFILT_VNODE,
	       EV_ADD | EV_ENABLE | EV_ONESHOT,
	       NOTE_DELETE | NOTE_WRITE | NOTE_EXTEND | NOTE_ATTRIB | NOTE_LINK | NOTE_RENAME | NOTE_REVOKE,
	       0, NULL);

	int nev = 0;
	while(true) {
		nev = kevent(mDescriptor, filters, 2, &event, 1, &mTimeOut);
		if(nev == -1)
			perror("kevent");
		else if (nev > 0) {
			if (event.fflags & NOTE_DELETE) {
				fprintf(stderr, "NOTE_DELETE ");
			}
			if (event.fflags & NOTE_EXTEND) {
				fprintf(stderr, "NOTE_EXTEND ");
			}
			if (event.fflags & NOTE_WRITE) {
				fprintf(stderr, "NOTE_WRITE ");
			}
			if (event.fflags & NOTE_ATTRIB) {
				fprintf(stderr, "NOTE_ATTRIB ");
			}
			if (event.fflags & NOTE_RENAME) {
				fprintf(stderr, "NOTE_RENAME ");
			}
		}
	}

//	Watcher watcher;
//	DirectoryWatch* dw = new DirectoryWatch("/Users/sradomski/Desktop/tmp", true);
//	dw->addMonitor(&watcher);
//	while(true) {
//		dw->updateEntries();
//	}
}