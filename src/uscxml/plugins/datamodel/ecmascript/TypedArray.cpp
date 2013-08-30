#include "TypedArray.h"
#include <iostream>

namespace uscxml {

unsigned long ArrayBuffer::getByteLength() {}
ArrayBuffer ArrayBuffer::slice(long begin, long end) {}
bool ArrayBuffer::isView(void*) {}
ArrayBuffer::operator bool() {}

ArrayBuffer ArrayBufferView::getBuffer() {}
unsigned long ArrayBufferView::getByteOffset() {}
unsigned long ArrayBufferView::getByteLength() {}

ArrayBuffer DataView::getBuffer() {}
unsigned long DataView::getByteOffset() {}
unsigned long DataView::getByteLength() {}
char DataView::getInt8(unsigned long) {}
unsigned char DataView::getUint8(unsigned long) {}
short DataView::getInt16(unsigned long, bool) {}
unsigned short DataView::getUint16(unsigned long, bool) {}
long DataView::getInt32(unsigned long, bool) {}
unsigned long DataView::getUint32(unsigned long, bool) {}
float DataView::getFloat32(unsigned long, bool) {}
double DataView::getFloat64(unsigned long, bool) {}
void DataView::setInt8(long, char) {}
void DataView::setUint8(long, unsigned char) {}
void DataView::setInt16(long, short, bool) {}
void DataView::setUint16(long, unsigned short, bool) {}
void DataView::setInt32(long, long, bool) {}
void DataView::setUint32(long, unsigned long, bool) {}
void DataView::setFloat32(long, float, bool) {}
void DataView::setFloat64(long, double, bool) {}

Uint8Array::Uint8Array(Uint8Array* other) {}
unsigned char Uint8Array::get(unsigned long) {}
void Uint8Array::set(unsigned long, char) {}
Uint8Array* Uint8Array::subarray(long, long) {}
unsigned long Uint8Array::getLength() {}

Uint8ClampedArray::Uint8ClampedArray(Uint8ClampedArray* other) {}
unsigned char Uint8ClampedArray::get(unsigned long) {}
void Uint8ClampedArray::set(unsigned long, char) {}
Uint8ClampedArray* Uint8ClampedArray::subarray(long, long) {}
unsigned long Uint8ClampedArray::getLength() {}

Int8Array::Int8Array(Int8Array* other) {}
char Int8Array::get(unsigned long) {}
void Int8Array::set(unsigned long, char) {}
Int8Array* Int8Array::subarray(long, long) {}
unsigned long Int8Array::getLength() {}

Int16Array::Int16Array(Int16Array* other) {}
short Int16Array::get(unsigned long) {}
void Int16Array::set(unsigned long, short) {}
Int16Array* Int16Array::subarray(long, long) {}
unsigned long Int16Array::getLength() {}

Uint16Array::Uint16Array(Uint16Array* other) {}
unsigned short Uint16Array::get(unsigned long) {}
void Uint16Array::set(unsigned long, unsigned short) {}
Uint16Array* Uint16Array::subarray(long, long) {}
unsigned long Uint16Array::getLength() {}

Int32Array::Int32Array(Int32Array* other) {}
long Int32Array::get(unsigned long) {}
void Int32Array::set(unsigned long, long) {}
Int32Array* Int32Array::subarray(long, long) {}
unsigned long Int32Array::getLength() {}

Uint32Array::Uint32Array(Uint32Array* other) {}
unsigned long Uint32Array::get(unsigned long) {}
void Uint32Array::set(unsigned long, unsigned long) {}
Uint32Array* Uint32Array::subarray(long, long) {}
unsigned long Uint32Array::getLength() {}

Float32Array::Float32Array(Float32Array* other) {}
float Float32Array::get(unsigned long) {}
void Float32Array::set(unsigned long, float) {}
Float32Array* Float32Array::subarray(long, long) {}
unsigned long Float32Array::getLength() {}

Float64Array::Float64Array(Float64Array* other) {}
double Float64Array::get(unsigned long) {}
void Float64Array::set(unsigned long, double) {}
Float64Array* Float64Array::subarray(long, long) {}
unsigned long Float64Array::getLength() {}

}