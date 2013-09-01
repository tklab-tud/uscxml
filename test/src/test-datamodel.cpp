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

	Interpreter interpreter = Interpreter::fromXML("<scxml></scxml>");
	DataModel dm(Factory::getInstance()->createDataModel("ecmascript", interpreter.getImpl().get()));
	dm.evalAsString("var foo = 12");

	// TypedArray tests
	// taken from https://bitbucket.org/lindenlab/llsd/src/
	{

		dm.evalAsBool("var a;");

		dm.evalAsBool("Int8Array.BYTES_PER_ELEMENT == 1");
		dm.evalAsBool("a = new Int8Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 1;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 8;"));

		dm.evalAsBool("Uint8Array.BYTES_PER_ELEMENT == 1");
		dm.evalAsBool("a = new Uint8Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 1;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 8;"));

		dm.evalAsBool("Int16Array.BYTES_PER_ELEMENT == 2");
		dm.evalAsBool("a = new Int16Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 2;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 16;"));

		dm.evalAsBool("Uint16Array.BYTES_PER_ELEMENT == 2");
		dm.evalAsBool("a = new Uint16Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 2;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 16;"));

		dm.evalAsBool("Int32Array.BYTES_PER_ELEMENT == 4");
		dm.evalAsBool("a = new Int32Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 4;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 32;"));

		dm.evalAsBool("Uint32Array.BYTES_PER_ELEMENT == 4");
		dm.evalAsBool("a = new Uint32Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 4;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 32;"));

		dm.evalAsBool("Float32Array.BYTES_PER_ELEMENT == 4");
		dm.evalAsBool("a = new Float32Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 4;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 32;"));

		dm.evalAsBool("Float64Array.BYTES_PER_ELEMENT == 8");
		dm.evalAsBool("a = new Float64Array([1, 2, 3, 4, 5, 6, 7, 8]);");
		assert(dm.evalAsBool("a.BYTES_PER_ELEMENT == 8;"));
		assert(dm.evalAsBool("a.byteOffset == 0;"));
		assert(dm.evalAsBool("a.byteLength == 64;"));

	}

	// ArrayBufferView
	{
		dm.evalAsBool("var ab = new ArrayBuffer(48);");
		dm.evalAsBool("var i32 = new Int32Array(ab, 16);");
		dm.evalAsBool("i32.set([1, 2, 3, 4, 5, 6, 7, 8]);");

//		assert(dm.evalAsBool("i32.buffer == ab;"));
		assert(dm.evalAsBool("i32.byteOffset == 16;"));
		assert(dm.evalAsBool("i32.byteLength == 32;"));

		dm.evalAsBool("var da = new DataView(i32.buffer, 8);");
//		assert(dm.evalAsBool("da.buffer == ab;"));
		assert(dm.evalAsBool("da.byteOffset == 8;"));
		assert(dm.evalAsBool("da.byteLength == 40;"));

	}

	// TypedArray constructors
	{
		assert(dm.evalAsBool("new Int8Array([0, 0, 0]).length == 3"));
		dm.evalAsBool("var rawbuf = (new Uint8Array([0, 1, 2, 3, 4, 5, 6, 7])).buffer");

		dm.evalAsBool("var int8 = new Int8Array(4);");
		assert(dm.evalAsBool("int8.BYTES_PER_ELEMENT == 1;"));
		assert(dm.evalAsBool("int8.length == 4;"));
		assert(dm.evalAsBool("int8.byteLength == 4;"));
		assert(dm.evalAsBool("int8.byteOffset == 0;"));
//		assert(dm.evalAsBool("int8.get(-1) == undefined;"));
//		assert(dm.evalAsBool("int8.get(4) == undefined;"));

		dm.evalAsBool("var int8 = new Int8Array([1, 2, 3, 4, 5, 6]);");
		assert(dm.evalAsBool("int8.length == 6;"));
		assert(dm.evalAsBool("int8.byteLength == 6;"));
		assert(dm.evalAsBool("int8.byteOffset == 0;"));
		assert(dm.evalAsBool("int8.get(3) == 4"));
		//		assert(dm.evalAsBool("int8.get(-1) == undefined;"));
		//		assert(dm.evalAsBool("int8.get(6) == undefined;"));

		dm.evalAsBool("var int8 = new Int8Array(rawbuf, 2);");
		assert(dm.evalAsBool("int8.length == 6;"));
		assert(dm.evalAsBool("int8.byteLength == 6;"));
		assert(dm.evalAsBool("int8.byteOffset == 2;"));
		assert(dm.evalAsBool("int8.get(5) == 7"));
		dm.evalAsBool("int8.set(0, 112)");
		assert(dm.evalAsBool("int8.get(0) == 112"));
		//		assert(dm.evalAsBool("int8.get(-1) == undefined;"));
		//		assert(dm.evalAsBool("int8.get(6) == undefined;"));

		dm.evalAsBool("var int8 = new Int8Array(rawbuf, 8);");
		assert(dm.evalAsBool("int8.length == 0;"));

		dm.evalAsBool("var int8 = new Int8Array(rawbuf, 2, 4);");
		assert(dm.evalAsBool("int8.length == 4;"));
		assert(dm.evalAsBool("int8.byteLength == 4;"));
		assert(dm.evalAsBool("int8.byteOffset == 2;"));
		assert(dm.evalAsBool("int8.get(3) == 5"));
		dm.evalAsBool("int8.set(0, 113)");
		assert(dm.evalAsBool("int8.get(0) == 113"));
		//		assert(dm.evalAsBool("int8.get(-1) == undefined;"));
		//		assert(dm.evalAsBool("int8.get(4) == undefined;"));

	}

	// TypedArray conversions
	{
		dm.evalAsBool("\
			function checkArray(typed_array, test) {\
				if(typed_array.length != test.length) { return false; }\
				for (var i = 0; i < test.length; i += 1) {\
					if(typed_array.get(i) != test[i]) { print(\"index \" + i + \": \" + typed_array.get(i) + \" != \" + test[i]); return false; }\
				}\
				return true;\
			}\
		");

		dm.evalAsBool("var uint8 = new Uint8Array([1, 2, 3, 4]);");
		dm.evalAsBool("var uint16 = new Uint16Array(uint8.buffer);");
		dm.evalAsBool("var uint32 = new Uint32Array(uint8.buffer);");

		assert(dm.evalAsBool("checkArray(uint8, [1, 2, 3, 4]);"));
		dm.evalAsBool("uint16.set(0, 0xffff);");
		assert(dm.evalAsBool("checkArray(uint8, [0xff, 0xff, 3, 4]);"));
		dm.evalAsBool("uint16.set(1, 0xeeee);");
		assert(dm.evalAsBool("checkArray(uint8, [0xff, 0xff, 0xee, 0xee]);"));
		dm.evalAsBool("uint32.set(0, 0x11111111);");
		assert(dm.evalAsBool("uint16.get(0) == 0x1111;"));
		assert(dm.evalAsBool("uint16.get(1) == 0x1111;"));
		assert(dm.evalAsBool("checkArray(uint8, [0x11, 0x11, 0x11, 0x11]);"));

	}

	// TypedArray signed/unsigned conversions
	{
		dm.evalAsBool("var int8 = new Int8Array(1)");
		dm.evalAsBool("var uint8 = new Uint8Array(int8.buffer);");
		dm.evalAsBool("uint8.set(0, 123);");
		assert(dm.evalAsBool("int8.get(0) == 123;"));
		dm.evalAsBool("uint8.set(0, 161);");
		assert(dm.evalAsBool("int8.get(0) == -95;"));
		dm.evalAsBool("int8.set(0, -120);");
		assert(dm.evalAsBool("uint8.get(0) == 136;"));
		dm.evalAsBool("int8.set(0, -1);");
		assert(dm.evalAsBool("uint8.get(0) == 0xff;"));

		dm.evalAsBool("var int16 = new Int16Array(1)");
		dm.evalAsBool("uint16 = new Uint16Array(int16.buffer);");
		dm.evalAsBool("uint16.set(0, 3210);");
		assert(dm.evalAsBool("int16.get(0) == 3210;"));
		dm.evalAsBool("uint16.set(0, 49232);");
		assert(dm.evalAsBool("int16.get(0), -16304;"));
		dm.evalAsBool("int16.set(0, -16384);");
		assert(dm.evalAsBool("uint16.get(0) == 49152;"));
		dm.evalAsBool("int16.set(0, -1);");
		assert(dm.evalAsBool("uint16.get(0) == 0xffff;"));

		dm.evalAsBool("var int32 = new Int32Array(1)");
		dm.evalAsBool("var uint32 = new Uint32Array(int32.buffer)");
		dm.evalAsBool("uint32.set(0, 0x80706050)");
		assert(dm.evalAsBool("int32.get(0) == -2140118960"));
		dm.evalAsBool("int32.set(0, -2023406815);");
		assert(dm.evalAsBool("uint32.get(0) == 0x87654321;"));
		dm.evalAsBool("int32.set(0, -1);");
		assert(dm.evalAsBool("uint32.get(0) == 0xffffffff;"));
	}

	// IEEE754 single precision parsing
	{
		dm.evalAsBool("\
			function fromBytes(bytes) {\
				var uint8 = new Uint8Array(bytes),\
				dv = new DataView(uint8.buffer);\
				return dv.getFloat32(0);\
			}\
		");

#if 0
		assert(dm.evalAsBool("fromBytes([0xff, 0xff, 0xff, 0xff]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0xff, 0xc0, 0x00, 0x01]) == NaN;"));

		assert(dm.evalAsBool("fromBytes([0xff, 0xc0, 0x00, 0x00]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0xff, 0xbf, 0xff, 0xff]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0xff, 0x80, 0x00, 0x01]) == NaN;"));

		assert(dm.evalAsBool("fromBytes([0xff, 0x80, 0x00, 0x00]) == -Infinity;"));

		assert(dm.evalAsBool("fromBytes([0xff, 0x7f, 0xff, 0xff]) == -3.4028234663852886E+38;"));
		assert(dm.evalAsBool("fromBytes([0x80, 0x80, 0x00, 0x00]) == -1.1754943508222875E-38;"));

		assert(dm.evalAsBool("fromBytes([0x80, 0x7f, 0xff, 0xff]) == -1.1754942106924411E-38;"));
		assert(dm.evalAsBool("fromBytes([0x80, 0x00, 0x00, 0x01]) == -1.4012984643248170E-45;"));

		assert(dm.evalAsBool("isNegativeZero(fromBytes([0x80, 0x00, 0x00, 0x00]));"));
		assert(dm.evalAsBool("isPositiveZero(fromBytes([0x00, 0x00, 0x00, 0x00]));"));

		assert(dm.evalAsBool("fromBytes([0x00, 0x00, 0x00, 0x01]) == 1.4012984643248170E-45;"));
		assert(dm.evalAsBool("fromBytes([0x00, 0x7f, 0xff, 0xff]) == 1.1754942106924411E-38;"));

		assert(dm.evalAsBool("fromBytes([0x00, 0x80, 0x00, 0x00]) == 1.1754943508222875E-38;"));
		assert(dm.evalAsBool("fromBytes([0x7f, 0x7f, 0xff, 0xff]) == 3.4028234663852886E+38;"));

		assert(dm.evalAsBool("fromBytes([0x7f, 0x80, 0x00, 0x00]) == +Infinity;"));

		assert(dm.evalAsBool("fromBytes([0x7f, 0x80, 0x00, 0x01]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0x7f, 0xbf, 0xff, 0xff]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0x7f, 0xc0, 0x00, 0x00]) == NaN;"));
		assert(dm.evalAsBool("fromBytes([0x7f, 0xff, 0xff, 0xff]) == NaN;"));
#endif

	}

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