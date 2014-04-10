#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;


int main(int argc, char** argv) {

	{
		PromelaParser ast("bit b;");
		ast.dump();
	}

	{
		PromelaParser ast1("a + (1 << b)");
		PromelaParser ast2("(a + 1) << b");
		ast1.dump();
		ast2.dump();
	}

	{
		PromelaParser ast("(b < N)");
		ast.dump();
	}

	{
		PromelaParser ast("i+1");
		ast.dump();
	}

	{
		PromelaParser ast("(mt+1)%MAX;");
		ast.dump();
	}

}