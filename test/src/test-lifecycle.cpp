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
	InterpreterState state;

	if (1) {
		// syntactic xml parse error
		const char* xml = "<invalid>";
		Interpreter interpreter = Interpreter::fromXML(xml);
		state = interpreter.getState();
		assert(!interpreter);
		assert(state == uscxml::InterpreterState::USCXML_FAULTED);
		std::cout << interpreter.getState() << std::endl;
	}

	if (1) {
		// semantic xml parse error
		const char* xml = "<invalid />";
		Interpreter interpreter = Interpreter::fromXML(xml);
		state = interpreter.getState();
		assert(state == uscxml::InterpreterState::USCXML_INSTANTIATED);
		
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FAULTED);
		std::cout << interpreter.getState() << std::endl;
	}

	if (1) {
		// single macrostep, multiple runs
		const char* xml =
		"<scxml>"
		"	<state id=\"start\">"
		"		<transition target=\"done\" />"
		" </state>"
		" <final id=\"done\" />"
		"</scxml>";

		Interpreter interpreter = Interpreter::fromXML(xml);
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
		interpreter.reset();
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
		interpreter.reset();
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
		interpreter.reset();
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
	}

	if (1) {
		// two microsteps
		const char* xml =
		"<scxml>"
		"	<state id=\"start\">"
		"		<transition target=\"s2\" />"
		" </state>"
		"	<state id=\"s2\">"
		"		<transition target=\"done\" />"
		" </state>"
		" <final id=\"done\" />"
		"</scxml>";
		
		Interpreter interpreter = Interpreter::fromXML(xml);
		
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
	}

	if (0) {
		// macrostep in between
		const char* xml =
		"<scxml>"
		"	<state id=\"start\">"
		"		<onentry>"
		"			<send event=\"continue\" delay=\"2s\"/>"
		"		</onentry>"
		"		<transition target=\"s2\" event=\"continue\" />"
		" </state>"
		"	<state id=\"s2\">"
		"		<transition target=\"done\" />"
		" </state>"
		" <final id=\"done\" />"
		"</scxml>";
		
		Interpreter interpreter = Interpreter::fromXML(xml);
		
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_IDLE);
		assert(interpreter.step(true) == uscxml::InterpreterState::USCXML_MACROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
		interpreter.reset();
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_IDLE);
		assert(interpreter.step(true) == uscxml::InterpreterState::USCXML_MACROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
	}

	if (1) {
		// macrostep in between, external event
		const char* xml =
		"<scxml>"
		"	<state id=\"start\">"
		"		<transition target=\"s2\" event=\"continue\" />"
		" </state>"
		"	<state id=\"s2\">"
		"		<transition target=\"done\" />"
		" </state>"
		" <final id=\"done\" />"
		"</scxml>";
		
		Interpreter interpreter = Interpreter::fromXML(xml);
		
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_IDLE);
		interpreter.receive(Event("continue"));
		assert(interpreter.step(true) == uscxml::InterpreterState::USCXML_MACROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
		interpreter.reset();
		assert(interpreter.getState() == uscxml::InterpreterState::USCXML_INSTANTIATED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_IDLE);
		interpreter.receive(Event("continue"));
		assert(interpreter.step(true) == uscxml::InterpreterState::USCXML_MACROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_MICROSTEPPED);
		assert(interpreter.step() == uscxml::InterpreterState::USCXML_FINISHED);
	}

	if (1) {
		// macrostep in between, external event
		const char* xml =
		"<scxml>"
		"	<state id=\"start\">"
		"		<transition target=\"s2\" event=\"continue\" />"
		" </state>"
		"	<state id=\"s2\">"
		"		<transition target=\"done\" />"
		" </state>"
		" <final id=\"done\" />"
		"</scxml>";
		
		Interpreter interpreter = Interpreter::fromXML(xml);
		interpreter.start();
		// assume interpreter is started
		assert(interpreter.getState() & InterpreterState::USCXML_THREAD_STARTED);
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(100));
		
		// assume it is started and running
		std::cout << interpreter.getState() << std::endl;
		
		assert(interpreter.getState() & InterpreterState::USCXML_THREAD_STARTED);
		assert(interpreter.getState() & InterpreterState::USCXML_THREAD_RUNNING);
		assert(interpreter.getState() & InterpreterState::USCXML_IDLE);

		interpreter.receive(Event("continue"));
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(200));

		std::cout << interpreter.getState() << std::endl;
		int state = interpreter.getState();
		assert(state & InterpreterState::USCXML_FINISHED);
		assert(!(state & InterpreterState::USCXML_THREAD_STARTED));
		assert(!(state & InterpreterState::USCXML_THREAD_RUNNING));

	}

	
	return EXIT_SUCCESS;
}