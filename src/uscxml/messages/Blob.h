/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef BLOB_H_E1B6D2C3
#define BLOB_H_E1B6D2C3

#include <string>
#include <memory>

#include "uscxml/Common.h"

namespace uscxml {

class USCXML_API BlobImpl {
public:
	BlobImpl(size_t size);
	BlobImpl(const char* data, size_t size, const std::string& mimeType, bool adopt = false);
	virtual ~BlobImpl();

	std::string base64() const;
	std::string md5() const;
	static BlobImpl* fromBase64(const std::string base64, const std::string& mimeType);

	char* getData() const {
		return data;
	}

	size_t getSize() const {
		return size;
	}

	std::string getMimeType() const {
		return mimeType;
	}

	void setMimeType(const std::string& mimeType) {
		this->mimeType = mimeType;
	}

#ifdef SWIGIMPORTED
protected:
#endif

	char* data;
	size_t size;
	std::string mimeType;
};

class USCXML_API Blob {
public:

	PIMPL_OPERATORS(Blob);

	Blob(size_t size) : _impl(std::shared_ptr<BlobImpl>(new BlobImpl(size))) {}
	Blob(const char* data,
	     size_t size,
	     const std::string& mimeType = "application/octet-stream",
	     bool adopt = false) :
		_impl(std::shared_ptr<BlobImpl>(new BlobImpl(data, size, mimeType, adopt))) {}

	static Blob fromBase64(const std::string base64, const std::string& mimeType = "application/octet-stream") {
		return Blob(std::shared_ptr<BlobImpl>(BlobImpl::fromBase64(base64, mimeType)));
	}

	std::string base64() const {
		return _impl->base64();
	}

	std::string md5() const {
		return _impl->md5();
	}

	char* getData() const {
		return _impl->getData();
	}

	size_t getSize() const {
		return _impl->getSize();
	}

	std::string getMimeType() const {
		return _impl->getMimeType();
	}

	void setMimeType(const std::string& mimeType) {
		_impl->setMimeType(mimeType);
	}

#ifdef SWIGIMPORTED
protected:
#endif
	std::shared_ptr<BlobImpl> _impl;

};

}

#endif /* end of include guard: BLOB_H_E1B6D2C3 */
