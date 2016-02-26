/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef TYPEDARRAY_H_99815BLY
#define TYPEDARRAY_H_99815BLY

#include "uscxml/Common.h"
#include "uscxml/messages/Blob.h"

#include <string>
#include <vector>
#include <boost/shared_ptr.hpp>
#include <string.h>
#include <inttypes.h>

#include <boost/type_traits.hpp>
#include <boost/static_assert.hpp>
#include <stdexcept>


namespace uscxml {

/**
 * https://www.khronos.org/registry/typedarray/specs/latest/
 */

class ArrayBuffer {
public:

	ArrayBuffer(void* data, unsigned int size);

	/**
	 * Creates a new ArrayBuffer of the given length in bytes. The contents of the
	 * ArrayBuffer are initialized to 0. If the requested number of bytes could not
	 * be allocated an exception is raised.
	 */
	ArrayBuffer(unsigned long length);
	ArrayBuffer(const Blob&);

	/**
	 * The length of the ArrayBuffer in bytes, as fixed at construction time.
	 * Reading this property returns 0 if this ArrayBuffer has been neutered.
	 */
	unsigned long getByteLength();

	/**
	 * Returns a new ArrayBuffer whose contents are a copy of this ArrayBuffer's
	 * bytes from begin, inclusive, up to end, exclusive. If either begin or end
	 * is negative, it refers to an index from the end of the array, as opposed
	 * to from the beginning.
	 * If end is unspecified, the new ArrayBuffer contains all bytes from begin
	 * to the end of this ArrayBuffer.
	 * The range specified by the begin and end values is clamped to the valid
	 * index range for the current array. If the computed length of the new
	 * ArrayBuffer would be negative, it is clamped to zero.
	 */
	ArrayBuffer slice(long begin, long end);
	ArrayBuffer slice(long begin);
	static bool isView(void*);
	unsigned long getLength() {
		return getByteLength();
	}
	operator bool();
	bool operator== (const ArrayBuffer& other) {
		return other._blob == _blob;
	}
//	unsigned char get(unsigned long index) {
//		if (index >= getLength())
//			return 0;
//		unsigned char retVal;
//		memcpy(&retVal, _blob->_data + index * sizeof(unsigned char), sizeof(unsigned char));
//		return retVal;
//	}
//
//	void set(unsigned long index, unsigned char value) {
//		memcpy(_blob->_data + index * sizeof(unsigned char), &value, sizeof(unsigned char));
//	}

	// non-standard extension
	std::string md5() const {
		return _blob.md5();
	}

	// non-standard extension
	std::string base64() const {
		return _blob.base64();
	}

	std::string getMimeType() const {
		if (_blob)
			return _blob.getMimeType();
		return "";
	}

	void setMimeType(const std::string& mimeType) {
		if (_blob)
			_blob.setMimeType(mimeType);
	}

	Blob _blob;
};

class ArrayBufferView {
public:
	virtual ~ArrayBufferView() {}
	/**
	 * The ArrayBuffer that this ArrayBufferView references.
	 */
	ArrayBuffer getBuffer();

	/**
	 * The offset of this ArrayBufferView from the start of its ArrayBuffer, in
	 * bytes, as fixed at construction time. Reading this property returns 0 if
	 * the referenced ArrayBuffer has been neutered.
	 */
	virtual unsigned long getByteOffset() = 0;

	/**
	 * The length of the ArrayBufferView in bytes, as fixed at construction time.
	 * Reading this property returns 0 if the referenced ArrayBuffer has been
	 * neutered.
	 */
	virtual unsigned long getByteLength() = 0;
	virtual unsigned long getLength() = 0;
protected:
	Blob _blob;
	unsigned long _start;
	unsigned long _end;
};


class DataView : ArrayBufferView {
public:
	/**
	 * Create a new DataView object using the passed ArrayBuffer for its storage.
	 * Optional byteOffset and byteLength can be used to limit the section of the
	 * buffer referenced. The byteOffset indicates the offset in bytes from the
	 * start of the ArrayBuffer, and the byteLength is the number of bytes from the
	 * offset that this DataView will reference. If both byteOffset and byteLength
	 * are omitted, the DataView spans the entire ArrayBuffer range. If the
	 * byteLength is omitted, the DataView extends from the given byteOffset until
	 * the end of the ArrayBuffer.
	 * If the given byteOffset and byteLength references an area beyond the end of
	 * the ArrayBuffer an exception is raised.
	 */

	DataView(ArrayBuffer*, unsigned long, unsigned long);
	DataView(ArrayBuffer*, unsigned long);
	DataView(ArrayBuffer*);

	unsigned long getByteOffset();
	unsigned long getByteLength();
	unsigned long getLength();

	/**
	 * Gets the value of the given type at the specified byte offset
	 * from the start of the view. There is no alignment constraint;
	 * multi-byte values may be fetched from any offset.
	 * For multi-byte values, the optional littleEndian argument
	 * indicates whether a big-endian or little-endian value should be
	 * read. If false or undefined, a big-endian value is read.
	 * These methods raise an exception if they would read
	 * beyond the end of the view.
	 */

	int8_t getInt8(unsigned long);
	uint8_t getUint8(unsigned long);
	int16_t getInt16(unsigned long, bool = false);
	uint16_t getUint16(unsigned long, bool = false);
	int32_t getInt32(unsigned long, bool = false);
	uint32_t getUint32(unsigned long, bool = false);
	float getFloat32(unsigned long, bool = false);
	double getFloat64(unsigned long, bool = false);

	/**
	 * Stores a value of the given type at the specified byte offset
	 * from the start of the view. There is no alignment constraint;
	 * multi-byte values may be stored at any offset.
	 * For multi-byte values, the optional littleEndian argument
	 * indicates whether the value should be stored in big-endian or
	 * little-endian byte order. If false or undefined, the value is
	 * stored in big-endian byte order.
	 * These methods raise an exception if they would write
	 * beyond the end of the view.
	 */

	void setInt8(long, int8_t);
	void setUint8(long, uint8_t);
	void setInt16(long, int16_t, bool = false);
	void setUint16(long, uint16_t, bool = false);
	void setInt32(long, int32_t, bool = false);
	void setUint32(long, uint32_t, bool = false);
	void setFloat32(long, float, bool = false);
	void setFloat64(long, double, bool = false);

};

template<class T, class S> class TypedArray : public ArrayBufferView {
public:
	virtual ~TypedArray() {}

	/**
	 * Create a new TypedArray object using the passed ArrayBuffer for its storage.
	 * Optional byteOffset and length can be used to limit the section of the buffer
	 * referenced. The byteOffset indicates the offset in bytes from the start of
	 * the ArrayBuffer, and the length is the count of elements from the offset
	 * that this TypedArray will reference. If both byteOffset and length are
	 * omitted, the TypedArray spans the entire ArrayBuffer range. If the length
	 * is omitted, the TypedArray extends from the given byteOffset until the end
	 * of the ArrayBuffer.
	 * The given byteOffset must be a multiple of the element size of the specific
	 * type, otherwise an exception is raised.
	 * If a given byteOffset and length references an area beyond the end of the
	 * ArrayBuffer an exception is raised.
	 * If length is not explicitly specified, the length of the ArrayBuffer minus
	 * the byteOffset must be a multiple of the element size of the specific type,
	 * or an exception is raised.
	 */
	TypedArray(uscxml::ArrayBuffer* buffer, unsigned long byteOffset, unsigned long length) {
		if (byteOffset % sizeof(S))
			return;

		_start = byteOffset / sizeof(S);
		_end = _start + length;

		if (_end > buffer->_blob._impl->size / sizeof(S))
			return;

		_blob = buffer->_blob;
	}
	TypedArray(uscxml::ArrayBuffer* buffer, unsigned long byteOffset) {
		if (byteOffset % sizeof(S))
			return;

		_start = byteOffset / sizeof(S);
		_end = buffer->_blob._impl->size / sizeof(S);
		_blob = buffer->_blob;
	}
	TypedArray(uscxml::ArrayBuffer* buffer) {
		_start = 0;
		_end = (buffer->_blob._impl->size) / sizeof(S);
		_blob = buffer->_blob;
	}

	TypedArray(Blob blob, unsigned long byteOffset, unsigned long length) {
		if (byteOffset % sizeof(S))
			return;

		_start = byteOffset / sizeof(S);
		_end = _start + length;

		if (_end > blob._impl->size / sizeof(S))
			return;

		_blob = blob;
	}

	/**
	 * Create a new ArrayBuffer with enough bytes to hold length elements of this
	 * typed array, then creates a typed array view referring to the full buffer.
	 * As with a directly constructed ArrayBuffer, the contents are initialized
	 * to 0. If the requested number of bytes could not be allocated an exception
	 * is raised.
	 */
	TypedArray(unsigned long length) {
		_start = 0;
		_end = length;
		_blob = Blob(length * sizeof(S));
	}

	/**
	 * Create a new ArrayBuffer with enough bytes to hold array.length elements of
	 * this typed array, then creates a typed array view referring to the full
	 * buffer. The contents of the new view are initialized to the contents of the
	 * given array or typed array, with each element converted to the appropriate
	 * typed array type.
	 */
	TypedArray(std::vector<T> data) {
		_start = 0;
		_end = data.size();
		_blob = Blob(data.size() * sizeof(S));
		set(data, 0);
	}
	TypedArray(TypedArray* other) {
		_start = other->_start;
		_end = other->_end;
		_blob = other->_blob;
	}

	/**
	 * This is an index getter.
	 * Returns the element at the given numeric index.
	 */
	T get(unsigned long index) {
		if (index >= getLength())
			return static_cast<T>(0);
		S retVal;
		memcpy(&retVal, _blob._impl->data + (_start + index) * sizeof(S), sizeof(S));
		return retVal;
	}

	/**
	 * This is an index setter.
	 * Sets the element at the given numeric index to the given value.
	 */
	void set(unsigned long index, T value) {
		memcpy(_blob._impl->data + (_start + index) * sizeof(S), &value, sizeof(S));
	}

	/**
	 * Set multiple values, reading input values from the array.
	 * The optional offset value indicates the index in the current array where
	 * values are written. If omitted, it is assumed to be 0.
	 * If the input array is a TypedArray, the two arrays may use the same
	 * underlying ArrayBuffer. In this situation, setting the values takes place
	 * as if all the data is first copied into a temporary buffer that does not
	 * overlap either of the arrays, and then the data from the temporary buffer
	 * is copied into the current array.
	 * If the offset plus the length of the given array is out of range for the
	 * current TypedArray, an exception is raised.
	 */
	void set(TypedArray<T, S>* value, unsigned long offset) {
		if (!_blob)
			return;
		if (offset * sizeof(S) + value->getByteLength() > _blob._impl->size)
			return;

		unsigned long otherOffset = value->_start * sizeof(S);

		// will this work if we use the same buffer?
		memcpy(_blob._impl->data + (_start + offset) * sizeof(S), value->_blob._impl->data + otherOffset, value->getByteLength());
	}

	void set(TypedArray<T, S>* value) {
		set(value, 0);
	}

	/**
	 * Set multiple values, reading input values from the array.
	 * The optional offset value indicates the index in the current array where
	 * values are written. If omitted, it is assumed to be 0.
	 * If the input array is a TypedArray, the two arrays may use the same
	 * underlying ArrayBuffer. In this situation, setting the values takes place
	 * as if all the data is first copied into a temporary buffer that does not
	 * overlap either of the arrays, and then the data from the temporary buffer
	 * is copied into the current array.
	 * If the offset plus the length of the given array is out of range for the
	 * current TypedArray, an exception is raised.
	 */
	void set(std::vector<T> data, unsigned long offset) {
		if (!_blob)
			return;
		if (data.size() + offset > _end)
			return;

		if (sizeof(T) == sizeof(S)) {
			memcpy(_blob._impl->data + offset, (void*)&data[0], data.size() * sizeof(S));
		} else {
			S* buffer = (S*)malloc(data.size() * sizeof(S));
			typename std::vector<T>::const_iterator dataIter = data.begin();
			unsigned long i = 0;
			while(dataIter != data.end()) {
				buffer[i] = *dataIter;
				dataIter++;
				i++;
			}
			memcpy(_blob._impl->data + offset, buffer, data.size() * sizeof(S));
			free (buffer);
		}
	}

	void set(std::vector<T> data) {
		set(data, 0);
	}

	/**
	 * Returns a new TypedArray view of the ArrayBuffer store for this TypedArray,
	 * referencing the elements at begin, inclusive, up to end, exclusive. If
	 * either begin or end is negative, it refers to an index from the end of the
	 * array, as opposed to from the beginning.
	 * If end is unspecified, the subarray contains all elements from begin to the
	 * end of the TypedArray.
	 * The range specified by the begin and end values is clamped to the valid
	 * index range for the current array. If the computed length of the new
	 * TypedArray would be negative, it is clamped to zero.
	 * The returned TypedArray will be of the same type as the array on which this
	 * method is invoked.
	 */
	TypedArray* subarray(long begin, long end) {
		if (!_blob)
			return NULL;
		unsigned int length = getLength();
		unsigned int realBegin = (begin + length) % length;
		unsigned int realEnd = (end + length) % length;
		if (realEnd == 0)
			realEnd = length;

		if (realEnd < realBegin)
			return NULL;

		return new TypedArray<T, S>(_blob, realBegin * sizeof(S), realEnd - realBegin);
	}

	TypedArray* subarray(long begin) {
		if (!_blob)
			return NULL;
		return subarray(begin, getLength());
	}

	unsigned long getLength() {
		if (!_blob)
			return 0;
		return _end - _start;
	}

	unsigned long getByteLength() {
		if (!_blob)
			return 0;
		return (_end - _start) * sizeof(S);
	}

	unsigned long getByteOffset() {
		if (!_blob)
			return 0;
		return _start * sizeof(S);
	}

};

/**
 * Define actual types as template instances.
 * First argument is representation from JavaScript, second type maybe smaller to
 * exactly specify the byte width ot the TypedArray.
 */
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
