#ifndef TYPEDARRAY_H_99815BLY
#define TYPEDARRAY_H_99815BLY

#include <string>
#include <map>

namespace uscxml {

class ArrayBuffer {
public:
	unsigned long getByteLength();
	ArrayBuffer slice(long begin, long end);
	static bool isView(void*);
	operator bool();
};

class ArrayBufferView {
public:
	ArrayBuffer getBuffer();
	unsigned long getByteOffset();
	unsigned long getByteLength();

};

class DataView {
public:
	ArrayBuffer getBuffer();
	unsigned long getByteOffset();
	unsigned long getByteLength();

	char getInt8(unsigned long);
	unsigned char getUint8(unsigned long);
	short getInt16(unsigned long, bool);
	unsigned short getUint16(unsigned long, bool);
	long getInt32(unsigned long, bool);
	unsigned long getUint32(unsigned long, bool);
	float getFloat32(unsigned long, bool);
	double getFloat64(unsigned long, bool);

	void setInt8(long, char);
	void setUint8(long, unsigned char);
	void setInt16(long, short, bool);
	void setUint16(long, unsigned short, bool);
	void setInt32(long, long, bool);
	void setUint32(long, unsigned long, bool);
	void setFloat32(long, float, bool);
	void setFloat64(long, double, bool);

};

class JSArray {
public:
	virtual unsigned long getLength() = 0;
protected:
	std::string _data;
};

class Uint8Array : public JSArray {
public:
	virtual ~Uint8Array() {}
	Uint8Array(Uint8Array* other);
	unsigned char get(unsigned long);
	void set(unsigned long, char);
	Uint8Array* subarray(long, long);
	unsigned long getLength();
};

class Uint8ClampedArray : public JSArray {
public:
	virtual ~Uint8ClampedArray() {}
	Uint8ClampedArray(Uint8ClampedArray* other);
	unsigned char get(unsigned long);
	void set(unsigned long, char);
	Uint8ClampedArray* subarray(long, long);
	unsigned long getLength();
};

class Int8Array : public JSArray {
public:
	virtual ~Int8Array() {}
	Int8Array(Int8Array* other);
	char get(unsigned long);
	void set(unsigned long, char);
	Int8Array* subarray(long, long);
	unsigned long getLength();
};

class Int16Array : public JSArray {
public:
	virtual ~Int16Array() {}
	Int16Array(Int16Array* other);
	short get(unsigned long);
	void set(unsigned long, short);
	Int16Array* subarray(long, long);
	unsigned long getLength();
};

class Uint16Array : public JSArray {
public:
	virtual ~Uint16Array() {}
	Uint16Array(Uint16Array* other);
	unsigned short get(unsigned long);
	void set(unsigned long, unsigned short);
	Uint16Array* subarray(long, long);
	unsigned long getLength();
};

class Int32Array : public JSArray {
public:
	virtual ~Int32Array() {}
	Int32Array(Int32Array* other);
	long get(unsigned long);
	void set(unsigned long, long);
	Int32Array* subarray(long, long);
	unsigned long getLength();
};

class Uint32Array : public JSArray {
public:
	virtual ~Uint32Array() {}
	Uint32Array(Uint32Array* other);
	unsigned long get(unsigned long);
	void set(unsigned long, unsigned long);
	Uint32Array* subarray(long, long);
	unsigned long getLength();
};

class Float32Array : public JSArray {
public:
	virtual ~Float32Array() {}
	Float32Array(Float32Array* other);
	float get(unsigned long);
	void set(unsigned long, float);
	Float32Array* subarray(long, long);
	unsigned long getLength();
};

class Float64Array : public JSArray {
public:
	virtual ~Float64Array() {}
	Float64Array(Float64Array* other);
	double get(unsigned long);
	void set(unsigned long, double);
	Float64Array* subarray(long, long);
	unsigned long getLength();
};
}

#endif /* end of include guard: TYPEDARRAY_H_99815BLY */
