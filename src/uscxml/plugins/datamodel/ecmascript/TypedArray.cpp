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

#include "TypedArray.h"
#include "uscxml/Convenience.h"
#include <iostream>

#define DATAVIEW_TYPED_GET(type) \
type retVal;\
if (index + _start + sizeof(type) > _buffer->size)\
	return 0;\
memcpy(&retVal, _buffer->data + (_start + index), sizeof(type));

#define DATAVIEW_TYPED_SET(type) \
if (index + _start + sizeof(type) > _buffer->size)\
	return;\
memcpy(_buffer->data + (_start + index), &value, sizeof(type));

namespace uscxml {

ArrayBuffer::ArrayBuffer(unsigned long length) {
	_buffer = boost::shared_ptr<Blob>(new Blob(length));
}

ArrayBuffer::ArrayBuffer(boost::shared_ptr<Blob> buffer) : _buffer(buffer) {
}

ArrayBuffer::ArrayBuffer(void* data, unsigned int size) {
	_buffer = boost::shared_ptr<Blob>(new Blob((const char*)data, size, "application/octet-stream"));
}

unsigned long ArrayBuffer::getByteLength() {
	if (!_buffer)
		return 0;
	return _buffer->size;
}

ArrayBuffer ArrayBuffer::slice(long begin, long end) {
	if (!_buffer) {
		return ArrayBuffer(0);
	}
	unsigned int realBegin = (begin + _buffer->size) % _buffer->size;
	unsigned int realEnd = (end + _buffer->size) % _buffer->size;
	if (realEnd < realBegin) {
		return ArrayBuffer(0);
	}

	ArrayBuffer arrBuffer(realEnd - realBegin);
	memcpy(arrBuffer._buffer->data, _buffer->data + realBegin, realEnd - realBegin);
	return arrBuffer;
}

ArrayBuffer ArrayBuffer::slice(long begin) {
	return slice(begin, _buffer->size);
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

DataView::DataView(ArrayBuffer* buffer, unsigned long byteOffset, unsigned long byteLength) {
	_start = byteOffset;
	if (_start > buffer->_buffer->size)
		return;
	_end = _start + byteLength;
	if (_end > buffer->_buffer->size)
		return;
	_buffer = buffer->_buffer;
}

DataView::DataView(ArrayBuffer* buffer , unsigned long byteOffset) {
	_start = byteOffset;
	_end = buffer->_buffer->size;
	if (_start > buffer->_buffer->size)
		return;
	_buffer = buffer->_buffer;
}

DataView::DataView(ArrayBuffer* buffer) {
	_start = 0;
	_end = (buffer->_buffer->size);
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

int8_t DataView::getInt8(unsigned long index) {
	DATAVIEW_TYPED_GET(int8_t);
	return retVal;
}

uint8_t DataView::getUint8(unsigned long index) {
	DATAVIEW_TYPED_GET(uint8_t);
	return retVal;
}

int16_t DataView::getInt16(unsigned long index, bool littleEndian) {
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

uint16_t DataView::getUint16(unsigned long index, bool littleEndian) {
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

int32_t DataView::getInt32(unsigned long index, bool littleEndian) {
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

uint32_t DataView::getUint32(unsigned long index, bool littleEndian) {
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

void DataView::setInt8(long index, int8_t value) {
	DATAVIEW_TYPED_SET(int8_t);
}

void DataView::setUint8(long index, uint8_t value) {
	DATAVIEW_TYPED_SET(uint8_t);
}

void DataView::setInt16(long index, int16_t value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(int16_t);
}

void DataView::setUint16(long index, uint16_t value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(uint16_t);
}

void DataView::setInt32(long index, int32_t value, bool littleEndian) {
#ifdef BOOST_LITTLE_ENDIAN
	if (!littleEndian)
		value = byte_swap<little_endian, big_endian>(value);
#else
	if (littleEndian)
		value = byte_swap<big_endian, little_endian>(value);
#endif
	DATAVIEW_TYPED_SET(int32_t);
}

void DataView::setUint32(long index, uint32_t value, bool littleEndian) {
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