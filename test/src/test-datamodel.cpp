#include "uscxml/URL.h"
#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include <SAX/helpers/InputSourceResolver.hpp>

#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;

class TestDataModelExtension : public DataModelExtension {
public:
	TestDataModelExtension() {}
	
	std::string provides() {
		return "_x.platform.pool";
	}
	
	Data getValueOf(const std::string& member) {
		return Data(true);
	}
	
	void setValueOf(const std::string& member, const Data& data) {
		std::cout << "Setting " << member << " to " << std::endl << Data::toJSON(data);
	}
};

int main(int argc, char** argv) {
#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif

	{
		char* testData = (char*)malloc(1024);
		for (int i = 0; i < 1024; i++) {
			testData[i] = (char)i;
		}

		Data data(testData, 1024, "", false);
		Blob blob = data.getBinary();
		char* otherData = blob.getData();

		for (int i = 0; i < 1024; i++) {
			assert(testData[i] == otherData[i]);
		}

	}

	Interpreter interpreter = Interpreter::fromXML("<scxml></scxml>", "");
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

	// TypedArray setting
	{
		dm.evalAsBool("var a = new Int32Array([1, 2, 3, 4, 5]);");
		dm.evalAsBool("var b = new Int32Array(5);");
		dm.evalAsBool("b.set(a);");
		assert(dm.evalAsBool("checkArray(b, [1, 2, 3, 4, 5]);"));

		dm.evalAsBool("b.set(new Int32Array([99, 98]), 2);");
		assert(dm.evalAsBool("checkArray(b, [1, 2, 99, 98, 5]);"));

		dm.evalAsBool("b.set(new Int32Array([99, 98, 97]), 2);");
		assert(dm.evalAsBool("checkArray(b, [1, 2, 99, 98, 97]);"));

		//  ab = [ 0, 1, 2, 3, 4, 5, 6, 7 ]
		//  a1 = [ ^, ^, ^, ^, ^, ^, ^, ^ ]
		//  a2 =             [ ^, ^, ^, ^ ]
		dm.evalAsBool("var ab = new ArrayBuffer(8);");
		dm.evalAsBool("var a1 = new Uint8Array(ab);");
		dm.evalAsBool("for (var i = 0; i < a1.length; i += 1) { a1.set(i, i); }");
		dm.evalAsBool("var a2 = new Uint8Array(ab, 4);");
		dm.evalAsBool("a1.set(a2, 2);");
		assert(dm.evalAsBool("checkArray(a1, [0, 1, 4, 5, 6, 7, 6, 7]);"));
		assert(dm.evalAsBool("checkArray(a2, [6, 7, 6, 7]);"));

	}

	// TypedArray.subarray
	{
		dm.evalAsBool("var a = new Int32Array([1, 2, 3, 4, 5]);");
		assert(dm.evalAsBool("checkArray(a.subarray(3), [4, 5]);"));
		assert(dm.evalAsBool("checkArray(a.subarray(1, 3), [2, 3]);"));
		assert(dm.evalAsBool("checkArray(a.subarray(-3), [3, 4, 5]);"));
		assert(dm.evalAsBool("checkArray(a.subarray(-3, -1), [3, 4]);"));
//		assert(dm.evalAsBool("checkArray(a.subarray(3, 2), []);"));
//		assert(dm.evalAsBool("checkArray(a.subarray(-2, -3), []);"));
//		assert(dm.evalAsBool("checkArray(a.subarray(4, 1), []);"));
//		assert(dm.evalAsBool("checkArray(a.subarray(-1, -4), []);"));

	}

	// DataView constructors
	{
		dm.evalAsBool("var d = new DataView(new ArrayBuffer(8));");

		dm.evalAsBool("d.setUint32(0, 0x12345678);");
		assert(dm.evalAsBool("d.getUint32(0), 0x12345678;"));

		dm.evalAsBool("d.setUint32(0, 0x12345678, true);");
		assert(dm.evalAsBool("d.getUint32(0, true), 0x12345678;"));

		dm.evalAsBool("d.setUint32(0, 0x12345678, true);");
		assert(dm.evalAsBool("d.getUint32(0), 0x78563412;"));

		dm.evalAsBool("d.setUint32(0, 0x12345678);");
		assert(dm.evalAsBool("d.getUint32(0, true), 0x78563412;"));

//		assertThrows('no arguments', TypeError, function() { return new DataView(); });
//		assertThrows('non-ArrayBuffer argument', TypeError, function() { return new DataView([]); });
//		assertThrows('non-ArrayBuffer argument', TypeError, function() { return new DataView("bogus"); });

	}

	// DataView accessors
	{
		dm.evalAsBool("var u = new Uint8Array(8), d = new DataView(u.buffer);");
		assert(dm.evalAsBool("checkArray(u, [0, 0, 0, 0, 0, 0, 0, 0]);"));

		dm.evalAsBool("d.setUint8(0, 255);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0, 0, 0, 0, 0, 0, 0]);"));

		dm.evalAsBool("d.setInt8(1, -1);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0xff, 0, 0, 0, 0, 0, 0]);"));

		dm.evalAsBool("d.setUint16(2, 0x1234);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0xff, 0x12, 0x34, 0, 0, 0, 0]);"));

		dm.evalAsBool("d.setInt16(4, -1);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0xff, 0x12, 0x34, 0xff, 0xff, 0, 0]);"));

		dm.evalAsBool("d.setUint32(1, 0x12345678);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0x12, 0x34, 0x56, 0x78, 0xff, 0, 0]);"));

		dm.evalAsBool("d.setInt32(4, -2023406815);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0x12, 0x34, 0x56, 0x87, 0x65, 0x43, 0x21]);"));

		dm.evalAsBool("d.setFloat32(2, 1.2E+38);");
		assert(dm.evalAsBool("checkArray(u, [0xff, 0x12, 0x7e, 0xb4, 0x8e, 0x52, 0x43, 0x21]);"));

		dm.evalAsBool("d.setFloat64(0, -1.2345678E+301);");
		assert(dm.evalAsBool("checkArray(u, [0xfe, 0x72, 0x6f, 0x51, 0x5f, 0x61, 0x77, 0xe5]);"));

		dm.evalAsBool("u.set([0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87]);");
		assert(dm.evalAsBool("d.getUint8(0) == 128;"));
		assert(dm.evalAsBool("d.getInt8(1) == -127;"));
		assert(dm.evalAsBool("d.getUint16(2) == 33411;"));
		assert(dm.evalAsBool("d.getInt16(3) == -31868;"));
		assert(dm.evalAsBool("d.getUint32(4) == 2223343239;"));
		assert(dm.evalAsBool("d.getInt32(2) == -2105310075;"));
		assert(dm.evalAsBool("d.getFloat32(2) == -1.932478247535851e-37;"));
		assert(dm.evalAsBool("d.getFloat64(0) == -3.116851295377095e-306;"));

	}

	// DataView endian
	{
		dm.evalAsBool("var rawbuf = (new Uint8Array([0, 1, 2, 3, 4, 5, 6, 7])).buffer;");
		dm.evalAsBool("var d;");

		dm.evalAsBool("d = new DataView(rawbuf);");
		assert(dm.evalAsBool("d.byteLength == 8;"));
		assert(dm.evalAsBool("d.byteOffset == 0;"));
//		assertThrows('bounds for buffer', DOMException, d.getUint8.bind(d), -2); // Chrome bug for index -1?
//		assertThrows('bounds for buffer', DOMException, d.getUint8.bind(d), 8);
//		assertThrows('bounds for buffer', DOMException, d.setUint8.bind(d), -2, 0);
//		assertThrows('bounds for buffer', DOMException, d.setUint8.bind(d), 8, 0);

		dm.evalAsBool("d = new DataView(rawbuf, 2);");
		assert(dm.evalAsBool("d.byteLength == 6;"));
		assert(dm.evalAsBool("d.byteOffset == 2;"));
		assert(dm.evalAsBool("d.getUint8(5) == 7;"));
//		assertThrows('bounds for buffer, byteOffset', DOMException, d.getUint8.bind(d), -2);
//		assertThrows('bounds for buffer, byteOffset', DOMException, d.getUint8.bind(d), 6);
//		assertThrows('bounds for buffer, byteOffset', DOMException, d.setUint8.bind(d), -2, 0);
//		assertThrows('bounds for buffer, byteOffset', DOMException, d.setUint8.bind(d), 6, 0);

		dm.evalAsBool("d = new DataView(rawbuf, 8);");
		assert(dm.evalAsBool("d.byteLength == 0;"));

//		assertThrows('invalid byteOffset', DOMException, function() { return new DataView(rawbuf, -1); });
//		assertThrows('invalid byteOffset', DOMException, function() { return new DataView(rawbuf, 9); });
//		assertThrows('invalid byteOffset', DOMException, function() { return new DataView(rawbuf, -1); });

		dm.evalAsBool("d = new DataView(rawbuf, 2, 4);");
		assert(dm.evalAsBool("d.byteLength == 4;"));
		assert(dm.evalAsBool("d.byteOffset == 2;"));
		assert(dm.evalAsBool("d.getUint8(3) == 5;"));
//		assertThrows('bounds for buffer, byteOffset, length', DOMException, function() { return d.getUint8(-2); });
//		assertThrows('bounds for buffer, byteOffset, length', DOMException, d.getUint8.bind(d), 4);
//		assertThrows('bounds for buffer, byteOffset, length', DOMException, d.setUint8.bind(d), -2, 0);
//		assertThrows('bounds for buffer, byteOffset, length', DOMException, d.setUint8.bind(d), 4, 0);

//		assertThrows('invalid byteOffset+length', DOMException, function() { return new DataView(rawbuf, 0, 9); });
//		assertThrows('invalid byteOffset+length', DOMException, function() { return new DataView(rawbuf, 8, 1); });
//		assertThrows('invalid byteOffset+length', DOMException, function() { return new DataView(rawbuf, 9, -1); });

	}

	// Typed Array getters/setters
	{

		dm.evalAsBool("var bytes = new Uint8Array([1, 2, 3, 4]);");
		dm.evalAsBool("var uint32s = new Uint32Array(bytes.buffer);");

		assert(dm.evalAsBool("bytes[1] == 2;"));
		dm.evalAsBool("uint32s[0] = 0xffffffff;");
		assert(dm.evalAsBool("bytes[1] == 0xff;"));

	}

	// string replacement
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
	
	{
		std::string xml =
		"<scxml datamodel=\"ecmascript\">"
		"  <script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />"
		"  <state id=\"s1\">"
		"    <onentry>"
		"      <script>_x.platform.pool('memeber.second', { foo: 12, bar: 34})</script>"
		"      <log label=\"ext\" expr=\"dump(_x.platform.pool('member.first'))\" />"
		"    </onentry>"
		"    <transition target=\"done\" />"
		"  </state>"
		"  <final id=\"done\" />"
		"</scxml>";

		TestDataModelExtension ext;
		Interpreter interpreter = Interpreter::fromXML(xml, "");
		interpreter.addDataModelExtension(&ext);

		InterpreterState state;

		do {
			state = interpreter.step();
		} while (state != USCXML_FINISHED && state!= USCXML_DESTROYED);

		
	}
}