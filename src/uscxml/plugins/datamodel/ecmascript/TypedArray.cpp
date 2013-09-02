#include "TypedArray.h"
#include <iostream>
#include <boost/detail/endian.hpp>

#define DATAVIEW_TYPED_GET(type) \
type retVal;\
memcpy(&retVal, _buffer->_data + (_start + index), sizeof(type));

#define DATAVIEW_TYPED_SET(type) \
memcpy(_buffer->_data + (_start + index), &value, sizeof(type));

namespace uscxml {

ArrayBuffer::Buffer::~Buffer() {
	free(_data);
}

ArrayBuffer::Buffer::Buffer(size_t size) {
	_data = (char*)malloc(size);
	memset(_data, 0, size);
	_size = size;
}

ArrayBuffer::Buffer::Buffer(void* data, size_t size) {
	_data = (char*)malloc(size);
	memcpy(_data, data, size);
	_size = size;
}

ArrayBuffer::ArrayBuffer(unsigned long length) {
	_buffer = boost::shared_ptr<Buffer>(new Buffer(length));
}

ArrayBuffer::ArrayBuffer(boost::shared_ptr<ArrayBuffer::Buffer> buffer) : _buffer(buffer) {
}

ArrayBuffer::ArrayBuffer(void* data, unsigned int size) {
	_buffer = boost::shared_ptr<Buffer>(new Buffer(data, size));
}

unsigned long ArrayBuffer::getByteLength() {
	if (!_buffer)
		return 0;
	return _buffer->_size;
}

ArrayBuffer ArrayBuffer::slice(long begin, long end) {
	if (!_buffer) {
		return ArrayBuffer(0);
	}
	unsigned int realBegin = (begin + _buffer->_size) % _buffer->_size;
	unsigned int realEnd = (end + _buffer->_size) % _buffer->_size;
	if (realEnd < realBegin) {
		return ArrayBuffer(0);
	}

	ArrayBuffer arrBuffer(realEnd - realBegin);
	memcpy(arrBuffer._buffer->_data, _buffer->_data + realBegin, realEnd - realBegin);
	return arrBuffer;
}

ArrayBuffer ArrayBuffer::slice(long begin) {
	return slice(begin, _buffer->_size);
}

bool ArrayBuffer::isView(void*) {
	return true;
}

ArrayBuffer::operator bool() {
	return _buffer;
}

ArrayBuffer ArrayBufferView::getBuffer() {
	return ArrayBuffer(_buffer);
}

DataView::DataView(ArrayBuffer* buffer, unsigned long start, unsigned long length) {
	_start = start;
	_end = start + length;
	_buffer = buffer->_buffer;
}

DataView::DataView(ArrayBuffer* buffer , unsigned long start) {
	_start = start;
	_end = buffer->_buffer->_size;
	_buffer = buffer->_buffer;
}

DataView::DataView(ArrayBuffer* buffer) {
	_start = 0;
	_end = (buffer->_buffer->_size);
	_buffer = buffer->_buffer;
}

unsigned long DataView::getByteOffset() {
	return _start;
}

unsigned long DataView::getByteLength() {
	return _end - _start;
}

unsigned long DataView::getLength() {
	return _end - _start;
}

char DataView::getInt8(unsigned long index) {
	DATAVIEW_TYPED_GET(int8_t);
	return retVal;
}

unsigned char DataView::getUint8(unsigned long index) {
	DATAVIEW_TYPED_GET(uint8_t);
	return retVal;
}

short DataView::getInt16(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(int16_t);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

unsigned short DataView::getUint16(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(uint16_t);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

long DataView::getInt32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(int32_t);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

unsigned long DataView::getUint32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(uint32_t);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

float DataView::getFloat32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(float);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

double DataView::getFloat64(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_GET(double);
#ifdef BOOST_LITTLE_ENDIAN
	if (littleEndian)
		return retVal;
	return byte_swap<little_endian, big_endian>(retVal);
#else
	if (littleEndian)
		return byte_swap<big_endian, little_endian>(retVal);
	return retVal;
#endif
}

void DataView::setInt8(long index, char value) {
	DATAVIEW_TYPED_SET(int8_t);
}

void DataView::setUint8(long index, unsigned char value) {
	DATAVIEW_TYPED_SET(uint8_t);
}

void DataView::setInt16(long index, short value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(int16_t);
}

void DataView::setUint16(long index, unsigned short value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(uint16_t);
}

void DataView::setInt32(long index, long value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(int32_t);
}

void DataView::setUint32(long index, unsigned long value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(uint32_t);
}

void DataView::setFloat32(long index, float value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(float);
}

void DataView::setFloat64(long index, double value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(double);
}

}