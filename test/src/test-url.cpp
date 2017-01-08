#include "uscxml/util/URL.h"
#include "uscxml/Interpreter.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/config.h"

#include <xercesc/parsers/XercesDOMParser.hpp>
#include "uscxml/interpreter/Logging.h"
#include <assert.h>
#include <iostream>

#include <sys/types.h>
#include <sys/stat.h>

using namespace uscxml;
using namespace XERCESC_NS;

class TestServlet : public HTTPServlet {
public:
	TestServlet(bool adaptPath) : _canAdaptPath(adaptPath) {}

	bool requestFromHTTP(const HTTPServer::Request& request) {
		return true;
	};
	bool canAdaptPath() {
		return _canAdaptPath;
	}
	void setURL(const std::string& url) {
		_actualUrl = url;
	}

	std::string _actualUrl;
	bool _canAdaptPath;
};

bool canResolve(const std::string& url) {
	URL absUrl(url);
	if (absUrl.scheme() == "") {
		absUrl = URL("file://" + url);
	}

	try {
		XercesDOMParser* parser = new XercesDOMParser();
		std::string tmp = absUrl;
		parser->parse(tmp.c_str());
		return true;
	} catch(...) {
		return false;
	}
}

bool dirExists(const std::string& path) {
#ifdef _WIN32
	DWORD ftyp = GetFileAttributesA(dirName_in.c_str());
	if (ftyp == INVALID_FILE_ATTRIBUTES)
		return false;  //something is wrong with your path!

	if (ftyp & FILE_ATTRIBUTE_DIRECTORY)
		return true;   // this is a directory!

	return false;    // this is not a directory!
#else
	struct stat info;

	if(stat( path.c_str(), &info ) != 0) {
		return false;
	} else if(info.st_mode & S_IFDIR) {
		return true;
	} else {
		return false;
	}
#endif
}

void testFileURLs() {

	// absolute
	std::list<URL> absURLs;
	{
		// with explicit file schema
		absURLs.push_back(URL("file:///"));
		absURLs.push_back(URL("file:/"));

		// platform specific
		absURLs.push_back(URL("file:/Z:/Windows/workspace/uscxml/bin/com/carmeq/scxml/test-xml-access.xml"));
		absURLs.push_back(URL("file:/C:/Windows/config.sys"));
		absURLs.push_back(URL("file:/Macintosh%20HD/fileURLs/text.txt"));
		absURLs.push_back(URL("file:/fileURLs/text.txt"));

		// usual filesystem paths
//		absURLs.push_back(URL("C:\\Windows\\sradomski\\Desktop\\foo.txt"));
//		absURLs.push_back(URL("C:\\Windows\\Some Spaces\\index.txt"));
//		absURLs.push_back(URL("C:/Windows/Some Spaces/index.txt"));
//		absURLs.push_back(URL("/Users/sradomski/Desktop/"));
//		absURLs.push_back(URL("/Users/sradomski/Desktop/foo.txt"));
	}

	std::list<URL> absWithHostURLs;
	{
		absWithHostURLs.push_back(URL("file://hostname/"));
		absWithHostURLs.push_back(URL("file://localhost/"));
		absWithHostURLs.push_back(URL("file://C:/config.sys"));
		absWithHostURLs.push_back(URL("file://config.sys"));
		absWithHostURLs.push_back(URL("file://config.sys"));
		absWithHostURLs.push_back(URL("file://Macintosh%20HD/fileURLs/text.txt"));
		absWithHostURLs.push_back(URL("file://fileURLs/text.txt"));
		absWithHostURLs.push_back(URL("file://Desktop/workspace/uscxml/bin/com/carmeq/scxml/test-xml-access.xml"));
		absWithHostURLs.push_back(URL("file://Windows\\sradomski\\Desktop\\foo.txt"));

	}
	// relative URLs
	std::list<URL> relURLs;

	{
		relURLs.push_back(URL("file"));
		relURLs.push_back(URL("file:"));
//		relURLs.push_back(URL("file://"));

		// platform specific
		relURLs.push_back(URL("file:Macintosh%20HD/fileURLs/text.txt"));
		relURLs.push_back(URL("file:fileURLs/text.txt"));
		relURLs.push_back(URL("file:Document/Text.foo"));

		// usual filesystem paths
		relURLs.push_back(URL("Users\\sradomski\\Desktop\\foo.txt"));
		relURLs.push_back(URL("Document\\Some Spaces\\index.txt"));
		relURLs.push_back(URL("Document/Some Spaces/index.txt"));
		relURLs.push_back(URL("Users/sradomski/Desktop/"));
		relURLs.push_back(URL("Users/sradomski/Desktop/foo.txt"));
	}

	for (std::list<URL>::iterator absIter = absURLs.begin(); absIter != absURLs.end(); absIter++) {
		std::cout << std::string(*absIter) << std::endl;
		assert(absIter->isAbsolute());
		assert(absIter->scheme() == "file");
		assert(absIter->host() == "");
	}

	for (std::list<URL>::iterator relIter = relURLs.begin(); relIter != relURLs.end(); relIter++) {
		std::cout << std::string(*relIter) << std::endl;
		assert(!relIter->isAbsolute());
	}

	for (std::list<URL>::iterator absIter = absURLs.begin(); absIter != absURLs.end(); absIter++) {
		for (std::list<URL>::iterator relIter = relURLs.begin(); relIter != relURLs.end(); relIter++) {
			URL tmp = URL::resolve(*relIter, *absIter);
			std::cout << std::string(tmp) << std::endl;
			assert(tmp.isAbsolute());
		}
	}

}

void testData() {
	{
		Data data = Data::fromJSON("{\"shiftKey\":false,\"toElement\":{\"id\":\"\",\"localName\":\"body\"},\"clientY\":38,\"y\":38,\"x\":66,\"ctrlKey\":false,\"relatedTarget\":{\"id\":\"\",\"localName\":\"body\"},\"clientX\":66,\"screenY\":288,\"metaKey\":false,\"offsetX\":58,\"altKey\":false,\"offsetY\":30,\"fromElement\":{\"id\":\"foo\",\"localName\":\"div\"},\"screenX\":-1691,\"dataTransfer\":null,\"button\":0,\"pageY\":38,\"layerY\":38,\"pageX\":66,\"charCode\":0,\"which\":0,\"keyCode\":0,\"detail\":0,\"layerX\":66,\"returnValue\":true,\"timeStamp\":1371223991895,\"eventPhase\":2,\"target\":{\"id\":\"foo\",\"localName\":\"div\"},\"defaultPrevented\":false,\"srcElement\":{\"id\":\"foo\",\"localName\":\"div\"},\"type\":\"mouseout\",\"cancelable\":true,\"currentTarget\":{\"id\":\"foo\",\"localName\":\"div\"},\"bubbles\":true,\"cancelBubble\":false}");
		std::cout << data << std::endl;
	}

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

}

void testHTTPURLs() {
	{
		URL url("http://www.heise.de/de/index.html");
		std::cout << std::string(url) << std::endl;
		assert(url.isAbsolute());
		assert(iequals(std::string(url), "http://www.heise.de/de/index.html"));
		assert(iequals(url.scheme(), "http"));
		assert(iequals(url.host(), "www.heise.de"));
		assert(iequals(url.path(), "/de/index.html"));
		url.download();
	}

	{
		try {
			URL url("http://asdfasdfasdfasdf.wgferg");
			std::cout << std::string(url) << std::endl;
			url.download(true);
			assert(false);
		} catch (Event e) {
		}
	}

	{
		try {
			URL url("http://uscxml.tk.informatik.tu-darmstadt.de/foobarfoo.html");
			std::cout << std::string(url) << std::endl;
			url.download(true);
			assert(false);
		} catch (Event e) {
			std::cout << e << std::endl;
		}
	}

#ifndef _WIN32
	// no SSL support on windows
	{
		URL url("https://raw.github.com/tklab-tud/uscxml/master/test/samples/uscxml/test-ecmascript.scxml");
		std::cout << std::string(url) << std::endl;
		assert(url.isAbsolute());
		assert(iequals(url.scheme(), "https"));
		url.download();
	}
#endif

}

void testServlets() {
	{
		TestServlet* testServlet1 = new TestServlet(false);
		TestServlet* testServlet2 = new TestServlet(false);

		assert(HTTPServer::registerServlet("/foo", testServlet1));
		assert(!HTTPServer::registerServlet("/foo", testServlet2));
		HTTPServer::unregisterServlet(testServlet1);
		assert(HTTPServer::registerServlet("/foo", testServlet2));
		HTTPServer::unregisterServlet(testServlet1);

		assert(HTTPServer::registerServlet("/foo/bar/", testServlet1));
		assert(!HTTPServer::registerServlet("/foo/bar/", testServlet2));
		HTTPServer::unregisterServlet(testServlet1);
		HTTPServer::unregisterServlet(testServlet2);
	}

}

void testPaths() {
	std::string resourceDir = URL::getResourceDir();
	std::cout << resourceDir << std::endl;
	assert(dirExists(resourceDir));

	std::string tmpPrivateDir = URL::getTempDir(false);
	std::cout << tmpPrivateDir << std::endl;
	assert(dirExists(tmpPrivateDir));

	std::string tmpSharedDir = URL::getTempDir(true);
	std::cout << tmpSharedDir << std::endl;
	assert(dirExists(tmpSharedDir));
}

int main(int argc, char** argv) {
#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif

	// some URLs from http://www-archive.mozilla.org/quality/networking/testing/filetests.html

	HTTPServer::getInstance(8199, 8200);

	try {
		testPaths();
		testFileURLs();
		testHTTPURLs();
		testData();
		testServlets();
	} catch (Event e) {
		LOGD(USCXML_ERROR) << e;
		exit(EXIT_FAILURE);
	}




}
