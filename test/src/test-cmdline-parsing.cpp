#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

int main(int argc, char** argv) {
	using namespace uscxml;

	if (true) {
		int testArgc = 11;
		const char* testArgv[] = {
			"test-cmdline-parsing",
			"--verbose",
			"--dot",
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
		assert(options.useDot);
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
		assert(options.interpreters.find("/foo/bar.scxml") != options.interpreters.end());
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
		assert(options.interpreters.find("/foo/bar1.scxml") != options.interpreters.end());
		assert(options.interpreters.find("/foo/bar2.scxml") != options.interpreters.end());
		assert(options.interpreters.find("/foo/bar3.scxml") != options.interpreters.end());
		assert(!options.interpreters["/foo/bar1.scxml"]->withHTTP);
		assert(options.interpreters["/foo/bar2.scxml"]->withHTTP);
		assert(!options.interpreters["/foo/bar3.scxml"]->withHTTP);
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
		assert(options.interpreters.find("/foo/bar1.scxml") != options.interpreters.end());
		assert(options.interpreters["/foo/bar1.scxml"]->additionalParameters.find("vrml-path") != options.interpreters["/foo/bar1.scxml"]->additionalParameters.end());
		assert(options.interpreters["/foo/bar1.scxml"]->additionalParameters.find("tmp-path") != options.interpreters["/foo/bar1.scxml"]->additionalParameters.end());
	}

	return EXIT_SUCCESS;
}