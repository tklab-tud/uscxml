#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#include <boost/algorithm/string.hpp>

int main(int argc, char** argv) {
	using namespace uscxml;

	if (true) {
		int testArgc = 11;
		const char* testArgv[] = {
			"test-cmdline-parsing",
			"--verbose",
			"--port=80",
			"--ssl-port=8080",
			"--certificate=/foo/bar.pem",
			"--private-key=/foo/bar.priv",
			"--public-key=/foo/bar.pub",
			"--plugin-path=/foo/plugins",
			"--loglevel=10",
			"--disable-http",
			0
		};
		InterpreterOptions options = InterpreterOptions::fromCmdLine(testArgc, (char **)testArgv);
		assert(options.verbose);
		assert(options.httpPort == 80);
		assert(options.httpsPort == 8080);
		assert(boost::equals(options.certificate, "/foo/bar.pem"));
		assert(boost::equals(options.privateKey, "/foo/bar.priv"));
		assert(boost::equals(options.publicKey, "/foo/bar.pub"));
		assert(boost::equals(options.pluginPath, "/foo/plugins"));
		assert(options.logLevel == 10);
		assert(!options.withHTTP);
		assert(!options); // invalid as no SCXML document is given
	}

	if (true) {
		int testArgc = 3;
		const char* testArgv[] = {
			"test-cmdline-parsing",
			"--verbose",
			"/foo/bar.scxml",
			0
		};
		InterpreterOptions options = InterpreterOptions::fromCmdLine(testArgc, (char **)testArgv);
		assert(options);
		assert(options.verbose);
		assert(options.interpreters.size() == 1);
		assert(options.interpreters.front().first == "/foo/bar.scxml");
	}

	if (true) {
		int testArgc = 7;
		const char* testArgv[] = {
			"test-cmdline-parsing",
			"--port=80",
			"/foo/bar1.scxml",
			"--disable-http",
			"/foo/bar2.scxml",
			"/foo/bar3.scxml",
			"--disable-http",
			0
		};
		InterpreterOptions options = InterpreterOptions::fromCmdLine(testArgc, (char **)testArgv);
		assert(options);
		assert(options.httpPort == 80);
		assert(options.interpreters.size() == 3);
		assert(options.interpreters[0].first == "/foo/bar1.scxml");
		assert(options.interpreters[1].first == "/foo/bar2.scxml");
		assert(options.interpreters[2].first == "/foo/bar3.scxml");

		assert(!options.interpreters[0].second->withHTTP);
		assert(options.interpreters[1].second->withHTTP);
		assert(!options.interpreters[2].second->withHTTP);
	}

	if (true) {
		int testArgc = 5;
		const char* testArgv[] = {
			"test-cmdline-parsing",
			"--port=80",
			"/foo/bar1.scxml",
			"--vrml-path=/foo/bar.test",
			"--tmp-path=/foo/bar.test",
			0
		};
		InterpreterOptions options = InterpreterOptions::fromCmdLine(testArgc, (char **)testArgv);
		assert(options);
		assert(options.httpPort == 80);
		assert(options.interpreters.size() == 1);
		assert(options.interpreters[0].first == "/foo/bar1.scxml");

		assert(options.interpreters[0].second->additionalParameters.find("vrml-path")
		       != options.interpreters[0].second->additionalParameters.end());
		assert(options.interpreters[0].second->additionalParameters.find("tmp-path")
		       != options.interpreters[0].second->additionalParameters.end());
	}

	return EXIT_SUCCESS;
}