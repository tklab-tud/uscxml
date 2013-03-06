#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

int main(int argc, char** argv) {

	{
		Data data = Data::fromJSON("asdf");
		std::cout << data << std::endl;
	}
	{
		Data data = Data::fromJSON("[ '1', '2', '3', '4' ]");
		std::cout << data << std::endl;
	}
	{
		Data data = Data::fromJSON("{'foo1': 'bar2', 'foo3': { 'foo4': 'bar5' }, 'foo6': 'bar7',  'foo8': { 'foo9': 'foo10': { 'foo11': 'bar12' } } }");
		std::cout << data << std::endl;
	}
	{
		Data data = Data::fromJSON("{\"firstName\": \"John\", \"lastName\": \"Smith\", \"age\": 25, \"address\": { \"streetAddress\": \"21 2nd Street\", \"city\": \"New York\",\"state\": \"NY\",\"postalCode\": 10021},\"phoneNumber\": [{\"type\": \"home\",\"number\": \"212 555-1234\"},{ \"type\": \"fax\",\"number\": \"646 555-4567\"}]}");
		std::cout << data << std::endl;
	}

	{
		URL url("http://www.heise.de/index.html");
		std::cout << url.asString() << std::endl;
		assert(url.isAbsolute());
		assert(iequals(url.scheme(), "http"));
		assert(iequals(url.host(), "www.heise.de"));
		assert(iequals(url.port(), "80"));
		assert(iequals(url.path(), "/index.html"));
		assert(iequals(url.asString(), "http://www.heise.de/index.html"));
	}
	{
		URL url("file:Document/Text.foo");
		std::cout << url.asString() << std::endl;
		assert(!url.isAbsolute());
		assert(iequals(url.scheme(), "file"));
		assert(iequals(url.host(), ""));
		assert(iequals(url.port(), "0"));
		assert(iequals(url.path(), "Document/Text.foo"));
		assert(iequals(url.asString(), "file:Document/Text.foo"));
	}
	{
		URL url("test/index.html");
		assert(iequals(url.scheme(), ""));
		url.toAbsoluteCwd();
		assert(iequals(url.scheme(), "file"));
		std::cout << url.asString() << std::endl;
	}
	{
		URL url("C:\\Document\\Some Spaces\\index.txt");
		assert(url.isAbsolute());
		assert(iequals(url.scheme(), "file"));
		std::cout << url.asString() << std::endl;
	}
	{
		URL url = URL::toLocalFile("this is quite some content!", "txt");
		std::cout << url.asLocalFile("txt");
		assert(url.isAbsolute());
		assert(iequals(url.scheme(), "file"));
	}
	{
		URL url("C:\\Document\\Some Spaces\\index.txt");
		assert(iequals(url.pathComponents()[0], "C:"));
		assert(iequals(url.pathComponents()[1], "Document"));
		assert(iequals(url.pathComponents()[2], "Some Spaces"));
		assert(iequals(url.pathComponents()[3], "index.txt"));
	}
}