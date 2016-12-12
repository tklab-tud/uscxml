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

#ifndef DATAMODELIMPL_H_5A33C087
#define DATAMODELIMPL_H_5A33C087

#include "uscxml/Common.h"
#include "uscxml/plugins/Invoker.h"
#include "uscxml/plugins/IOProcessor.h"
#include "uscxml/interpreter/Logging.h"

namespace XERCESC_NS {
class DOMDocument;
class DOMNode;
}

#include <list>
#include <string>
#include <memory>

namespace uscxml {

class InterpreterImpl;
class DataModelImpl;

/**
 * @ingroup datamodel
 * @ingroup callback
 * Callbacks available for every data-model.
 */
class USCXML_API DataModelCallbacks {
public:
	virtual ~DataModelCallbacks() {} ///< silence virtual destructor warning from swig
	virtual const std::string& getName() = 0;
	virtual const std::string& getSessionId() = 0;
	virtual const std::map<std::string, IOProcessor>& getIOProcessors() = 0;
	virtual bool isInState(const std::string& stateId) = 0;
	virtual XERCESC_NS::DOMDocument* getDocument() const = 0;
	virtual const std::map<std::string, Invoker>& getInvokers() = 0;
	virtual Logger getLogger() = 0;
};

class USCXML_API DataModelExtension {
public:
	DataModelExtension() : dm(NULL) {}
	virtual ~DataModelExtension() {}
	virtual std::string provides() = 0;
	virtual Data invoke(const std::string& member, const Data& params) = 0;
	virtual Data getValueOf(const std::string& member) = 0;
	virtual void setValueOf(const std::string& member, const Data& data) = 0;
	DataModelImpl* dm;
};

/**
 * @ingroup datamodel
 * @ingroup abstract
 * Abstract base class for all data-model implementations.
 */
class USCXML_API DataModelImpl {
public:
	virtual ~DataModelImpl() {}

	/**
	 * The Factory wants to instantiate a new instance.
	 * This function will have to initialize the object. The actual constructor
	 * is called from within here. The only one who calls the constructor directly
	 * is the Factory for the prototype object.
	 *
	 * @param callbacks The callbacks available to the datamodel
	 * @return A shared pointer with an initialized instance
	 */
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks) = 0;

	/**
	 * Return a list of names to be matched by the `datamodel` attribute in SCXML.
	 */
	virtual std::list<std::string> getNames() = 0;

	/**
	 * Determine whether a given string constitutes valid syntax in the
	 * data-model's language.
	 * @param expr A string, supposedly containing an expression of the data-model.
	 * @return Whether expr is in L(DM).
	 */
	virtual bool isValidSyntax(const std::string& expr) {
		return true; // overwrite when datamodel supports it
	}

	/**
	 * Set the given event as `_event` in the data-model's global scope.
	 * @param event The event as it was dequeued from either the internal or external queue.
	 */
	virtual void setEvent(const Event& event) = 0;

	/**
	 * Experimental extension to have dynamic content in string literals.
	 * This function was used to replace ${foo} expressions on the data-model,
	 * e.g. in text nodes. It will eventually make a reappearance I guess.
	 * @param content The string with tokens to replace.
	 * @return How many occurences where replaced.
	 */
	size_t replaceExpressions(std::string& content);

	/**
	 * Evaluate the given expression as something iterable and return its length.
	 * @param expr Anything that possibly evaluates to an enumerable object.
	 * @return The number of items in the enumerable object.
	 */
	virtual uint32_t getLength(const std::string& expr) = 0;

	/**
	 * Set a given item to the object at a given index for one iteration.
	 * @param item A variable or location to assign the current object to.
	 * @param array An expression evalating to an enumerable object.
	 * @param index A variable or location to set the current index at.
	 * @param iteration The current iteration index.
	 */
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) = 0;

	/**
	 * Return a string as an *unevaluated* Data object.
	 * @param content A string with a literal, eppression or compound data-structure in the data-model's language.
	 * @return An unevaluated structure representing the given compound or literal.
	 */
	virtual Data getAsData(const std::string& content) = 0;

	/**
	 * Return a string as an *evaluated* Data object.
	 * @param content A string with a literal, eppression or compound data-structure in the data-model's language.
	 * @return An evaluated structure representing the given compound or literal.
	 */
	virtual Data evalAsData(const std::string& content) = 0;

	/**
	 * Evaluate a given expression as a boolean.
	 * This function is a subset of evalAsData() but saves on creating and copying a Data object.
	 * @param expr An expression in the data-model's language.
	 * @return Whether the expression evaluates as `true`
	 */
	virtual bool evalAsBool(const std::string& expr) = 0;

	/**
	 * Determine whether a given variable / location is declared.
	 * @param expr The variable / location to check.
	 * @todo Is this still used?
	 */
	virtual bool isDeclared(const std::string& expr) = 0;

	/**
	 * Assign a data object to a location in the data-model.
	 * There are different occurences in the SCXML IRP tests, e.g.
	\verbatim
	test147:
	<data id="Var1" expr="0"/>

	test150:
	<data id="Var3">
	[1,2,3]
	</data>

	test277:
	<data id="Var1" expr="return"/>
	\endverbatim
	 * @param location A variable or locatio to assign to.
	 * @param data The Data object with the respective data.
	 */
	virtual void assign(const std::string& location, const Data& data) = 0;

	/**
	 * Initialize a variable / location in the data-model with a given data object.
	 * This is, semantically, very close to assign() but does not assume the
	 * location to be declared first.
	 *
	 * @param location A variable or locatio to assign to.
	 * @param data The Data object with the respective data.
	 */
	virtual void init(const std::string& location, const Data& data) = 0;

	/**
	 * Register an extension to get data into and out of the data-model.
	 * @todo This is currently unsupported
	 */
	virtual void addExtension(DataModelExtension* ext);

	/**
	 * Concat the given terms into a conjunctive form.
	 * @todo This is required to automatically transform a state-chart into a
	 * state-machine. Actual transformation is still only available in legacy though.
	 */
	virtual std::string andExpressions(std::list<std::string>) {
		return "";
	}

protected:
	DataModelCallbacks* _callbacks;
};

}

#endif /* end of include guard: DATAMODELIMPL_H_5A33C087 */
