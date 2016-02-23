// I feel dirty, but we need to access the datamodel timer
// #define protected public

#include "uscxml/config.h"

#ifdef APPLE
#include <mach/mach.h>
#include <mach/mach_time.h>
#include <pthread.h>
#endif

#include "uscxml/Common.h"
#include "uscxml/Convenience.h"

#ifdef BUILD_PROFILING
// get access to the datamodel - this causes strange issues with MSVC depending on include order
// may be better to ifndef all protected: and private: stanzas for profiling?
#define protected public
#include "uscxml/Interpreter.h"
#undef protected
# endif


#include "uscxml/dom/DOMUtils.h"
#include "uscxml/concurrency/Timer.h"

#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/transform/ChartToFlatSCXML.h"
#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef BUILD_PROFILING
#   include "uscxml/plugins/DataModel.h"
# endif

#ifdef _WIN32
#include "XGetopt.h"
#include "XGetopt.cpp"
#endif

static bool withFlattening = false;
static double delayFactor = 1;
static size_t benchmarkRuns = 1;
static std::string documentURI;

int retCode = EXIT_FAILURE;
uscxml::Interpreter interpreter;

void printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-f] [-dN] [-bN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" URL");
	printf("\n");
	printf("Options\n");
	printf("\t-f             : flatten to SCXML state-machine\n");
	printf("\t-d FACTOR      : delay factor\n");
	printf("\t-b ITERATIONS  : benchmark with number of runs\n");
	printf("\n");
	exit(1);
}

class W3CStatusMonitor : public uscxml::InterpreterMonitor {

	void beforeCompletion(uscxml::Interpreter tmp) {
		if (interpreter.getConfiguration().size() == 1 && interpreter.isInState("pass")) {
#ifndef BUILD_PROFILING
			std::cout << "TEST SUCCEEDED" << std::endl;
#endif
			retCode = EXIT_SUCCESS;
			return;
		}
#ifndef BUILD_PROFILING
		std::cout << "TEST FAILED" << std::endl;
#endif
		retCode = EXIT_FAILURE;
	}
};

int main(int argc, char** argv) {
	using namespace uscxml;

#ifdef APPLE
	mach_timebase_info_data_t timebase_info;
	mach_timebase_info(&timebase_info);

	const uint64_t NANOS_PER_MSEC = 1000000ULL;
	double clock2abs = ((double)timebase_info.denom / (double)timebase_info.numer) * NANOS_PER_MSEC;

	thread_time_constraint_policy_data_t policy;
	policy.period      = 0;
	policy.computation = (uint32_t)(5 * clock2abs); // 5 ms of work
	policy.constraint  = (uint32_t)(10 * clock2abs);
	policy.preemptible = FALSE;

	int kr = thread_policy_set(pthread_mach_thread_np(pthread_self()),
	                           THREAD_TIME_CONSTRAINT_POLICY,
	                           (thread_policy_t)&policy,
	                           THREAD_TIME_CONSTRAINT_POLICY_COUNT);
	if (kr != KERN_SUCCESS) {
		mach_error("thread_policy_set:", kr);
		exit(1);
	}
#endif

	try {

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
		signal(SIGPIPE, SIG_IGN);
#endif

		if (argc < 2) {
			exit(EXIT_FAILURE);
		}

		google::InitGoogleLogging(argv[0]);

		HTTPServer::getInstance(32954, 32955, NULL); // bind to some random tcp sockets for ioprocessor tests

		char* dfEnv = getenv("USCXML_DELAY_FACTOR");
		if (dfEnv) {
			delayFactor = strTo<double>(dfEnv);
		}

		const char* envBenchmarkRuns = getenv("USCXML_BENCHMARK_ITERATIONS");
		if (envBenchmarkRuns != NULL) {
			benchmarkRuns = strTo<size_t>(envBenchmarkRuns);
			google::SetStderrLogging(3);
		} else {
			google::LogToStderr();
		}

		int option;
		while ((option = getopt(argc, argv, "fd:b:")) != -1) {
			switch(option) {
			case 'f':
				withFlattening = true;
				break;
			case 'd':
				delayFactor = strTo<double>(optarg);
				break;
			case 'b':
				benchmarkRuns = strTo<size_t>(optarg);
				break;
			default:
				break;
			}
		}

		documentURI = argv[optind];

		LOG(INFO) << "Processing " << documentURI << (withFlattening ? " FSM converted" : "") << (delayFactor ? "" : " with delays *= " + toStr(delayFactor)) << (benchmarkRuns > 0 ? " for " + toStr(benchmarkRuns) + " benchmarks" : "");
		if (withFlattening) {
			interpreter = Interpreter::fromURL(documentURI);
			Transformer flattener = ChartToFlatSCXML::transform(interpreter);
			interpreter = flattener;
//			std::cout << interpreter.getDocument() << std::endl;
		} else {
			interpreter = Interpreter::fromURL(documentURI);
		}

		if (delayFactor != 1) {
			Arabica::DOM::Document<std::string> document = interpreter.getDocument();
			Arabica::DOM::Element<std::string> root = document.getDocumentElement();
			Arabica::XPath::NodeSet<std::string> sends = DOMUtils::filterChildElements(interpreter.getNameSpaceInfo().xmlNSPrefix + "send", root, true);

			for (int i = 0; i < sends.size(); i++) {
				Arabica::DOM::Element<std::string> send = Arabica::DOM::Element<std::string>(sends[i]);
				if (HAS_ATTR(send, "delay")) {
					NumAttr delay(ATTR(send, "delay"));
					int value = strTo<int>(delay.value);
					if (delay.unit == "s")
						value *= 1000;
					value *= delayFactor;
					send.setAttribute("delay", toStr(value) + "ms");
					std::cout << ATTR(send, "delay") << std::endl;
				} else if (HAS_ATTR(send, "delayexpr")) {
					std::string delayExpr = ATTR(send, "delayexpr");
					send.setAttribute("delayexpr",
					                  "(" + delayExpr + ".indexOf('ms', " + delayExpr + ".length - 2) !== -1 ? "
					                  "(" + delayExpr + ".slice(0,-2) * " + toStr(delayFactor) + ") + \"ms\" : "
					                  "(" + delayExpr + ".slice(0,-1) * 1000 * " + toStr(delayFactor) + ") + \"ms\")");
					std::cout << ATTR(send, "delayexpr") << std::endl;
				}
			}
			std::list<InterpreterIssue> issues = interpreter.validate();
			for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
				std::cout << *issueIter << std::endl;
			}
		}

		if (interpreter) {
			W3CStatusMonitor* vm = new W3CStatusMonitor();
			interpreter.addMonitor(vm);

			LOG(INFO) << "Benchmarking " << documentURI << (withFlattening ? " FSM converted" : "") << (delayFactor ? "" : " with delays *= " + toStr(delayFactor));

			size_t remainingRuns = benchmarkRuns;
			size_t microSteps = 0;

			Timer tTotal;
			tTotal.start();

			double avg = 0;
#ifdef BUILD_PROFILING
			double avgDm = 0;
			double avgStep = 0;
#endif

			while(remainingRuns-- > 0) {
				Timer t;
				microSteps = 0;

				InterpreterState state = interpreter.getState();

				for(;;) {
					state = interpreter.step(true);
					microSteps++;
					if (state == USCXML_INITIALIZED) {
						t.start();
					} else if (state == USCXML_FINISHED) {
#ifdef BUILD_PROFILING
						avgDm += interpreter._impl->_dataModel.timer.elapsed;
						interpreter._impl->_dataModel.timer.reset();
						avgStep += interpreter.timer.elapsed;
#endif
					}
					if (state < 0)
						break;
				}
				assert(retCode == EXIT_SUCCESS);
				t.stop();
				avg += t.elapsed;
				interpreter.reset();
				std::cout << "." << std::flush;
			}

			tTotal.stop();

			std::cout << benchmarkRuns << " iterations" << std::endl;
			std::cout << tTotal.elapsed * 1000.0 << " ms in total" << std::endl;
			std::cout << (avg * 1000.0) / (double)benchmarkRuns << " ms per execution" << std::endl;
			std::cout << microSteps << " microsteps per iteration" << std::endl;
			std::cout << (avg * 1000.0) / ((double)benchmarkRuns * (double)microSteps) << " ms per microstep" << std::endl;
#ifdef BUILD_PROFILING
			std::cout << (avgDm * 1000.0) / (double)benchmarkRuns << " ms in datamodel" << std::endl;
			std::cout << ((avg - avgDm) * 1000.0) / ((double)benchmarkRuns * (double)microSteps) << " ms per microstep \\wo datamodel" << std::endl;
#endif
		}
	} catch(Event e) {
		std::cout << e << std::endl;
	} catch(std::exception e) {
		std::cout << e.what() << std::endl;
	}
	return retCode;
}
