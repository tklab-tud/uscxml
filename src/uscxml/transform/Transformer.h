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

#ifndef TRANSFORMER_H_32113356
#define TRANSFORMER_H_32113356

#include <iostream>
#include <map>
#include "uscxml/Interpreter.h"

namespace uscxml {

class USCXML_API TransformerImpl {
public:
	TransformerImpl() {}

	virtual void writeTo(std::ostream& stream) = 0;
	virtual operator Interpreter() {
		throw std::runtime_error("Transformer cannot be interpreted as an Interpreter again");
	}

protected:
    std::multimap<std::string, std::string> _extensions;
    std::list<std::string> _options;
    
    friend class Transformer;
};

class USCXML_API Transformer : public boost::enable_shared_from_this<Transformer> {
public:
//	Transformer(const Interpreter& source) { _impl = new (source) }

	Transformer() : _impl() {} // the empty, invalid interpreter
	Transformer(boost::shared_ptr<TransformerImpl> const impl) : _impl(impl) { }
	Transformer(const Transformer& other) : _impl(other._impl) { }
	virtual ~Transformer() {};

	operator bool() const {
		return (_impl);
	}
	bool operator< (const Transformer& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const Transformer& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const Transformer& other) const     {
		return _impl != other._impl;
	}
	Transformer& operator= (const Transformer& other)   {
		_impl = other._impl;
		return *this;
	}

	virtual void writeTo(std::ostream& stream) {
		_impl->writeTo(stream);
	}
	operator Interpreter() {
		return _impl->operator Interpreter();
	}

	boost::shared_ptr<TransformerImpl> getImpl() {
		return _impl;
	}

    void setExtensions(const std::multimap<std::string, std::string>& extensions) {
        _impl->_extensions = extensions;
    }
    
    void setOptions(const std::list<std::string>& options) {
        _impl->_options = options;
    }
    
protected:
	boost::shared_ptr<TransformerImpl> _impl;

};

}

#endif /* end of include guard: TRANSFORMER_H_32113356 */
