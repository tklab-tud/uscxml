#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/server/HTTPServer.h"

#include <SAX/helpers/InputSourceResolver.hpp>

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;


int main(int argc, char** argv) {
#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif
	
	DataModel dm(Factory::getInstance()->createDataModel("ecmascript", NULL));
	dm.evalAsString("var foo = 12");

	{
		std::string content = "$";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 0);
		std::cout << content << std::endl;
		assert(boost::equals(content, "$"));
	}

	{
		std::string content = "$sadf ${foo}";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 1);
		std::cout << content << std::endl;
		assert(boost::equals(content, "$sadf 12"));
	}

	{
		std::string content = "${";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 0);
		std::cout << content << std::endl;
		assert(boost::equals(content, "${"));
	}

	{
		std::string content = "${foo}";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 1);
		std::cout << content << std::endl;
		assert(boost::equals(content, "12"));
	}

	{
		std::string content = "${bar}";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 0);
		std::cout << content << std::endl;
		assert(boost::equals(content, "${bar}"));
	}
	
	{
		std::string content = "There are ${bar} monkeys! Really ${foo} monkeys!";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 1);
		std::cout << content << std::endl;
		assert(boost::equals(content, "There are ${bar} monkeys! Really 12 monkeys!"));
	}

	{
		std::string content = "There are ${foo} monkeys! Really ${foo} monkeys!";
		int rplc = dm.replaceExpressions(content);
		assert(rplc == 2);
		std::cout << content << std::endl;
		assert(boost::equals(content, "There are 12 monkeys! Really 12 monkeys!"));
	}
}