#ifndef TYPEDARRAY_H_99815BLY
#define TYPEDARRAY_H_99815BLY

#include <string>
#include <vector>
#include <boost/shared_ptr.hpp>
#include <string.h>
#include <inttypes.h>


namespace uscxml {

class ArrayBuffer {
public:
	class Buffer {
	public:
		~Buffer();
		Buffer(size_t size);
		Buffer(void* data, size_t size);
		char* _data;
		size_t _size;
	};

	ArrayBuffer(void* data, unsigned int size);
	ArrayBuffer(unsigned long length);
	ArrayBuffer(boost::shared_ptr<ArrayBuffer::Buffer>);
	unsigned long getByteLength();
	ArrayBuffer slice(long begin, long length);
	ArrayBuffer slice(long begin);
	static bool isView(void*);
	unsigned long getLength() {
		return getByteLength();
	}
	operator bool();
	bool operator== (const ArrayBuffer& other) {
		return other._buffer == _buffer;
	}
	unsigned char get(unsigned long index) {
		if (index >= getLength())
			return 0;
		unsigned char retVal;
		memcpy(&retVal, _buffer->_data + index * sizeof(unsigned char), sizeof(unsigned char));
		return retVal;
	}

	void set(unsigned long index, unsigned char value) {
		memcpy(_buffer->_data + index * sizeof(unsigned char), &value, sizeof(unsigned char));
	}

	boost::shared_ptr<Buffer> _buffer;
};

class ArrayBufferView {
public:
	virtual ~ArrayBufferView() {}
	ArrayBuffer getBuffer();
	virtual unsigned long getByteOffset() = 0;
	virtual unsigned long getByteLength() = 0;
	virtual unsigned long getLength() = 0;
protected:
	boost::shared_ptr<ArrayBuffer::Buffer> _buffer;
	unsigned long _start;
	unsigned long _end;
};

class DataView : ArrayBufferView {
public:
	DataView(ArrayBuffer*, unsigned long, unsigned long);
	DataView(ArrayBuffer*, unsigned long);
	DataView(ArrayBuffer*);

	unsigned long getByteOffset();
	unsigned long getByteLength();
	unsigned long getLength();

	char getInt8(unsigned long);
	unsigned char getUint8(unsigned long);
	short getInt16(unsigned long, bool = false);
	unsigned short getUint16(unsigned long, bool = false);
	long getInt32(unsigned long, bool = false);
	unsigned long getUint32(unsigned long, bool = false);
	float getFloat32(unsigned long, bool = false);
	double getFloat64(unsigned long, bool = false);

	void setInt8(long, char);
	void setUint8(long, unsigned char);
	void setInt16(long, short, bool = false);
	void setUint16(long, unsigned short, bool = false);
	void setInt32(long, long, bool = false);
	void setUint32(long, unsigned long, bool = false);
	void setFloat32(long, float, bool = false);
	void setFloat64(long, double, bool = false);

};

template<class T, class S> class TypedArray : public ArrayBufferView {
public:
	virtual ~TypedArray() {}
	TypedArray(uscxml::ArrayBuffer* buffer, unsigned long start, unsigned long length) {
		_start = start;
		_end = start + length;
		_buffer = buffer->_buffer;
	}
	TypedArray(uscxml::ArrayBuffer* buffer, unsigned long start) {
		_start = start / sizeof(S);
		_end = buffer->_buffer->_size / sizeof(S);
		_buffer = buffer->_buffer;
	}
	TypedArray(uscxml::ArrayBuffer* buffer) {
		_start = 0;
		_end = (buffer->_buffer->_size) / sizeof(S);
		_buffer = buffer->_buffer;
	}

	TypedArray(boost::shared_ptr<ArrayBuffer::Buffer> buffer, unsigned long start, unsigned long length) {
		_start = start;
		_end = start + length;
		_buffer = buffer;
	}
	TypedArray(unsigned long length) {
		_start = 0;
		_end = length;
		_buffer = boost::shared_ptr<ArrayBuffer::Buffer>(new ArrayBuffer::Buffer(length * sizeof(S)));
	}
	TypedArray(std::vector<T> data) {
		_start = 0;
		_end = data.size();
		if (sizeof(T) == sizeof(S)) {
			_buffer = boost::shared_ptr<ArrayBuffer::Buffer>(new ArrayBuffer::Buffer(((void*)&data[0]), data.size() * sizeof(T)));
		} else {
			S* buffer = (S*)malloc(data.size() * sizeof(S));
			typename std::vector<T>::const_iterator dataIter = data.begin();
			unsigned long i = 0;
			while(dataIter != data.end()) {
				buffer[i] = *dataIter;
				dataIter++;
				i++;
			}
			_buffer = boost::shared_ptr<ArrayBuffer::Buffer>(new ArrayBuffer::Buffer(buffer, data.size() * sizeof(S)));
		}
	}
	TypedArray(TypedArray* other) {
		_start = other->_start;
		_end = other->_end;
		_buffer = other->_buffer;
	}
	T get(unsigned long index) {
		if (index >= getLength())
			return static_cast<T>(0);
		S retVal;
		memcpy(&retVal, _buffer->_data + (_start + index) * sizeof(S), sizeof(S));
		return retVal;
	}
	void set(unsigned long index, T value) {
		memcpy(_buffer->_data + (_start + index) * sizeof(S), &value, sizeof(S));
	}

	void set(TypedArray<T, S>* value, unsigned long offset) {
		memcpy(_buffer->_data + (_start) * sizeof(S), &value->_buffer->_data[offset], value->_buffer->_size);
	}

	void set(TypedArray<T, S>* value) {
		set(value, 0);
	}

	void set(std::vector<T> data, unsigned long offset) {
	}

	void set(std::vector<T> data) {
		set(data, 0);
	}

	TypedArray* subarray(long start, long end) {
		return new TypedArray<T, S>(_buffer, start, end);
	}

	unsigned long getLength() {
		return _end - _start;
	}

	unsigned long getByteLength() {
		return (_end - _start) * sizeof(S);
	}

	unsigned long getByteOffset() {
		return _start * sizeof(S);
	}


};

typedef TypedArray<unsigned char, uint8_t> Uint8Array;
typedef TypedArray<unsigned char, uint8_t> Uint8ClampedArray;
typedef TypedArray<char, int8_t> Int8Array;
typedef TypedArray<short, int16_t> Int16Array;
typedef TypedArray<unsigned short, uint16_t> Uint16Array;
typedef TypedArray<long, int32_t> Int32Array;
typedef TypedArray<unsigned long, uint32_t> Uint32Array;
typedef TypedArray<float, float> Float32Array;
typedef TypedArray<double, double> Float64Array;

}

#endif /* end of include guard: TYPEDARRAY_H_99815BLY */
