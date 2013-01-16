#include "uscxml/URL.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

int main(int argc, char** argv) {
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
}