#include "TypedArray.h"
#include <iostream>

#define DATAVIEW_TYPED_RETURN(type) \
type retVal;\
memcpy(&retVal, _buffer->_data + (_start + index), sizeof(type));\
return retVal;

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

unsigned long ArrayBuffer::getByteLength() {
	return _buffer->_size;
}

ArrayBuffer ArrayBuffer::slice(long begin, long length) {
	ArrayBuffer arrBuffer(length);
	memcpy(arrBuffer._buffer->_data, _buffer->_data + begin, length);
	return arrBuffer;
}

ArrayBuffer ArrayBuffer::slice(long begin) {
	return slice(begin, _buffer->_size - begin);
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
	DATAVIEW_TYPED_RETURN(int8_t);
}

unsigned char DataView::getUint8(unsigned long index) {
	DATAVIEW_TYPED_RETURN(uint8_t);
}

short DataView::getInt16(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(int16_t);
}

unsigned short DataView::getUint16(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(uint16_t);
}

long DataView::getInt32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(int32_t);
}

unsigned long DataView::getUint32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(uint32_t);
}

float DataView::getFloat32(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(float);
}

double DataView::getFloat64(unsigned long index, bool littleEndian) {
	DATAVIEW_TYPED_RETURN(double);
}

void DataView::setInt8(long index, char value) {
	DATAVIEW_TYPED_SET(int8_t);
}

void DataView::setUint8(long index, unsigned char value) {
	DATAVIEW_TYPED_SET(uint8_t);
}

void DataView::setInt16(long index, short value, bool) {
	DATAVIEW_TYPED_SET(int16_t);
}
void DataView::setUint16(long index, unsigned short value, bool littleEndian) {
	DATAVIEW_TYPED_SET(uint16_t);
}

void DataView::setInt32(long index, long value, bool littleEndian) {
	DATAVIEW_TYPED_SET(int32_t);
}

void DataView::setUint32(long index, unsigned long value, bool littleEndian) {
	DATAVIEW_TYPED_SET(uint32_t);
}

void DataView::setFloat32(long index, float value, bool littleEndian) {
	DATAVIEW_TYPED_SET(float);
}

void DataView::setFloat64(long index, double value, bool littleEndian) {
	DATAVIEW_TYPED_SET(double);
}

}