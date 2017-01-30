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

#include <map>
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"

namespace uscxml {

class USCXML_API TransformerImpl {
public:
	TransformerImpl(const Interpreter& other) {
		interpreter = other; // we need to keep a reference to retain the document!
		other.getImpl()->setupDOM();
		_document = other.getImpl()->_document;
		_baseURL = other.getImpl()->_baseURL;
		_scxml =  other.getImpl()->_scxml;
		_name =  other.getImpl()->_name;
		_binding = other.getImpl()->_binding;
	}



	virtual void writeTo(std::ostream& stream) = 0;
	virtual operator Interpreter() {
		throw std::runtime_error("Transformer cannot be interpreted as an Interpreter again");
	}

	virtual XERCESC_NS::DOMDocument* getDocument() const {
		return _document;
	}

protected:
	std::multimap<std::string, std::string> _extensions;
	std::list<std::string> _options;

	XERCESC_NS::DOMDocument* _document;
	XERCESC_NS::DOMElement* _scxml;

	Interpreter interpreter;
	InterpreterImpl::Binding _binding;
	URL _baseURL;
	std::string _name;

	friend class Transformer;
};

class USCXML_API Transformer {
public:
//	Transformer(const Interpreter& source) { _impl = new (source) }

	Transformer() : _impl() {} // the empty, invalid interpreter
	Transformer(std::shared_ptr<TransformerImpl> const impl) : _impl(impl) { }
	Transformer(const Transformer& other) : _impl(other._impl) { }
	virtual ~Transformer() {};

	operator bool() const {
		return !!_impl;
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

	std::shared_ptr<TransformerImpl> getImpl() {
		return _impl;
	}

	void setExtensions(const std::multimap<std::string, std::string>& extensions) {
		_impl->_extensions = extensions;
	}

	void setOptions(const std::list<std::string>& options) {
		_impl->_options = options;
	}

protected:
	std::shared_ptr<TransformerImpl> _impl;

};

}

#endif /* end of include guard: TRANSFORMER_H_32113356 */
