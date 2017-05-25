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

#ifndef DATA_H_09E4D8E5
#define DATA_H_09E4D8E5

#include <list>
#include <map>
#include <memory>
#include <type_traits>

#include "uscxml/Common.h"
#include "uscxml/util/Convenience.h"
#include "uscxml/messages/Blob.h"

//#include <xercesc/dom/DOMDocument.hpp>

// forward declare
namespace XERCESC_NS {
class DOMDocument;
class DOMNode;
}

namespace uscxml {

static unsigned int _dataIndentation = 1;

class USCXML_API Data {
public:
	enum Type {
		VERBATIM,
		INTERPRETED,
	};

	Data() : node(NULL), type(INTERPRETED) {
		// silence stupid not used error for statics in gcc
		(void)_dataIndentation;
	}

	explicit Data(const char* data, size_t size, const std::string& mimeType, bool adopt = false);

	// convenience constructors
//	explicit Data(bool atom) : node(NULL), type(VERBATIM) {
//		if (atom) {
//			this->atom = "true";
//		} else {
//			this->atom = "false";
//		}
//	}

	explicit Data(XERCESC_NS::DOMNode* node_) : node(node_) {}

	explicit Data(const std::string& value) : node(NULL), atom(toStr(value)), type(VERBATIM) {}


#ifndef SWIGIMPORTED
	// swig barfs on this one, have them explictly
	template <
	    typename T,
	    typename = typename std::enable_if<std::is_arithmetic<T>::value, T>::type
	    >
	explicit Data(T value)
		: node(NULL), atom(toStr(value)), type(INTERPRETED) {}
#endif

	template <typename T>
	explicit Data(T value, Type type) : node(NULL), atom(toStr(value)), type(type) {}

	~Data() {
	}

	void clear() {
		type = VERBATIM;
		compound.clear();
		array.clear();
		atom.clear();
		binary = Blob();
		node = NULL;
	}

	bool empty() const {
		bool hasContent = (atom.length() > 0 || !compound.empty() || !array.empty() || binary || node);
		return !hasContent;
	}

	bool operator<(const Data& other) const {
		if (other.atom != atom)
			return other.atom < atom;
		if (other.array != array)
			return other.array < array;
		if (other.compound != compound)
			return other.compound < compound;
		if (other.node != node)
			return other.node < node;
		if (other.binary != binary)
			return other.binary < binary;
		if (other.type != type)
			return other.type < type;

		return false;
	}

	void merge(const Data& other);

	bool hasKey(const std::string& key) const {
		return (!compound.empty() && compound.find(key) != compound.end());
	}

#ifndef SWIGIMPORTED

	Data& operator[](const std::string& key) {
		return compound[key];
	}

	Data& operator[](const char* key) {
		return compound[key];
	}

	const Data& operator[](const std::string& key) const {
		return compound.at(key);
	}

	const Data& operator[](const char* key) const {
		return compound.at(key);
	}

	Data& operator[](const size_t index) {
		return array.at(index);
	}
#endif

	const Data at(const std::string& key) const {
		return at(key.c_str());
	}

	const Data at(const char* key) const {
		if (hasKey(key))
			return compound.at(key);
		Data data;
		return data;
	}

	const Data item(const size_t index) const {
		auto it = array.find(index);
		if (it != array.end()) {
			return it->second;
		}
		Data data;
		return data;
	}

	void put(std::string key, const Data& data) {
		compound[key] = data;
	}

	void put(size_t index, const Data& data) {
		this[index] = data;
	}

	bool operator==(const Data &other) const {
		return !(*this != other);
	}

	bool operator!=(const Data &other) const {
		return (*this < other || other < *this);
	}

	operator std::string() const {
		return atom;
	}

	operator std::map<std::string, Data>() {
		return compound;
	}

	operator std::map<int,Data>() {
		return array;
	}

	static Data fromJSON(const std::string& jsonString);
	static std::string toJSON(const Data& data);
	std::string asJSON() const;

	std::map<int,Data> getArray() {
		return array;
	}
	void setArray(const std::map<int,Data>& array) {
		this->array = array;
	}

	std::string getAtom() const {
		return atom;
	}
	void setAtom(const std::string& atom) {
		this->atom = atom;
	}

	Blob getBinary() {
		return this->binary;
	}
	void setBinary(const Blob& binary) {
		this->binary = binary;
	}

	Type getType() {
		return type;
	}
	void setType(const Type type) {
		this->type = type;
	}

	// Bug in SWIG 3.0.8 Python: Data in a map has to be fully qualified!
	std::map<std::string, uscxml::Data> getCompound() {
		return compound;
	}

	void setCompound(const std::map<std::string, uscxml::Data>& compound) {
		this->compound = compound;
	}

#ifdef SWIGIMPORTED
protected:
#endif

	XERCESC_NS::DOMNode* node;
//	std::shared_ptr<XERCESC_NS::DOMDocument> adoptedDoc;
	std::map<std::string, Data> compound;
	std::map<int,Data> array;
	std::string atom;
	Blob binary;
	Type type;

protected:
	static std::string jsonEscape(const std::string& expr);
	static std::string jsonUnescape(const std::string& expr);
	friend USCXML_API std::ostream& operator<< (std::ostream& os, const Data& data);

};

USCXML_API std::ostream& operator<< (std::ostream& os, const Data& data);

}

#endif /* end of include guard: DATA_H_09E4D8E5 */
