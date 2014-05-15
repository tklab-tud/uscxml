#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"
#include <boost/algorithm/string.hpp>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
#endif

#ifdef _WIN32
#include "XGetopt.h"
#endif

int startedAt;
int lastTransitionAt;

#ifdef HAS_EXECINFO_H
void printBacktrace(void** array, int size) {
	char** messages = backtrace_symbols(array, size);
	for (int i = 0; i < size && messages != NULL; ++i) {
		std::cerr << "\t" << messages[i] << std::endl;
	}
	std::cerr << std::endl;
	free(messages);
}

#ifdef HAS_DLFCN_H
// see https://gist.github.com/nkuln/2020860
typedef void (*cxa_throw_type)(void *, void *, void (*) (void *));
cxa_throw_type orig_cxa_throw = 0;

void load_orig_throw_code() {
	orig_cxa_throw = (cxa_throw_type) dlsym(RTLD_NEXT, "__cxa_throw");
}

extern "C"
void __cxa_throw (void *thrown_exception, void *pvtinfo, void (*dest)(void *)) {
	std::cerr << __FUNCTION__ << " will throw exception from " << std::endl;
	if (orig_cxa_throw == 0)
		load_orig_throw_code();
	
	void *array[50];
	size_t size = backtrace(array, 50);
	printBacktrace(array, size);
	orig_cxa_throw(thrown_exception, pvtinfo, dest);
}
#endif
#endif


// see http://stackoverflow.com/questions/2443135/how-do-i-find-where-an-exception-was-thrown-in-c
void customTerminate() {
	static bool tried_throw = false;
	try {
		// try once to re-throw currently active exception
		if (!tried_throw) {
			throw;
			tried_throw = true;
		} else {
			tried_throw = false;
		};
	} catch (const std::exception &e) {
		std::cerr << __FUNCTION__ << " caught unhandled exception. what(): "
		<< e.what() << std::endl;
	} catch (const uscxml::Event &e) {
		std::cerr << __FUNCTION__ << " caught unhandled exception. Event: "
		<< e << std::endl;
	} catch (...) {
		std::cerr << __FUNCTION__ << " caught unknown/unhandled exception."
		<< std::endl;
	}
	
#ifdef HAS_EXECINFO_H
	void * array[50];
	int size = backtrace(array, 50);
	
	printBacktrace(array, size);
#endif
	abort();
}
int main(int argc, char** argv) {
	using namespace uscxml;
	
	std::set_terminate(customTerminate);
	
#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif
		
	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();
	
	Interpreter interpreter = Interpreter::fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test530.scxml");
	InterpreterState state;
	do {
		state = interpreter.step(true);
		switch (state) {
			case uscxml::FINISHED:
				std::cout << "FINISHED" << std::endl;
				break;
			case uscxml::INIT_FAILED:
				std::cout << "INIT_FAILED" << std::endl;
				break;
			case uscxml::NOTHING_TODO:
				std::cout << "NOTHING_TODO" << std::endl;
				break;
			case uscxml::INTERRUPTED:
				std::cout << "INTERRUPTED" << std::endl;
				break;
			case uscxml::PROCESSED:
				std::cout << "PROCESSED" << std::endl;
				break;
			default:
				break;
		}
	} while(state != FINISHED);
	
	return EXIT_SUCCESS;
}