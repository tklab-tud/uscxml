/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef INTERPRETER_H_6CD5A168
#define INTERPRETER_H_6CD5A168


#include "Common.h"

#include <map>
#include <string>
#include <vector>

#include "uscxml/interpreter/MicroStep.h"
#include "uscxml/interpreter/Logging.h"
#include "uscxml/plugins/DataModel.h"
#include "uscxml/plugins/Factory.h"
#include "uscxml/interpreter/ContentExecutor.h"
#include "uscxml/interpreter/EventQueue.h"
#include "uscxml/interpreter/InterpreterState.h"

#ifdef max
#error define NOMINMAX or undefine the max macro please (https://support.microsoft.com/en-us/kb/143208)
#endif

namespace uscxml {

class InterpreterMonitor;
class InterpreterImpl;
class InterpreterIssue;


/**
 * @ingroup interpreter
 * Collection of instances for interpreter that constitute its action language.
 */
class USCXML_API ActionLanguage {
public:
	Logger logger; ///< The logger instance to use for messages
	MicroStep microStepper; ///< The microstepper instance to use
	DataModel dataModel; ///< The datamodel to use
	ContentExecutor execContent; ///< To process executable content elements
	EventQueue internalQueue; ///< The queue where internal events will be enqueued
	EventQueue externalQueue; ///< The queue for external events
	DelayedEventQueue delayedQueue; ///< The queue for delayed events
};

/**
 * @ingroup interpreter
 * @ingroup facade
 * Central class to interpret and process SCXML documents.

	 Instances of this class are available from the static constructors. In order
	 to use an interpreter instance to actually *do* things, you will want to
	 provide an ActionLanguage and an InterpreterMonitor.

	 We did avoid threading primitives within the core interpreter (there is
	 threading for nested interpeters in the USCXMLInvoker, though). As such, you
	 will have to call the <step> function continuously.

 */

class USCXML_API Interpreter {
public:

	/**
	 * Instantiate an Interpeter with a given XML document.
	 * @param dom A pointer to the XML document.
	 * @param baseURL An absolute URL to resolve relative URLs in the document.
	 * @param copy Whether to make a copy of the document, we deallocate it either way.
	 */
	static Interpreter fromDocument(XERCESC_NS::DOMDocument* dom,
	                                const std::string& baseURL,
	                                bool copy = true);
	/**
	 * Instantiate an Interpeter with a given XML element.
	 * This constructor will create a new document and copy/import the given element.
	 * @param element The element to be copies/imported as the new document element.
	 * @param baseURL An absolute URL to resolve relative URLs in the document.
	 */
	static Interpreter fromElement(XERCESC_NS::DOMElement* element,
	                               const std::string& baseURL);
	/**
	 * Instantiate an Interpeter from a string containined proper XML markup.
	 * @param xml Textual representation of an SCXML document.
	 * @param baseURL An absolute URL to resolve relative URLs in the document.
	 */
	static Interpreter fromXML(const std::string& xml,
	                           const std::string& baseURL);
	/**
	 * Instantiate an Interpeter with a document located at an URL.
	 * @param url An absolute URL to locate the SCXML document.
	 */
	static Interpreter fromURL(const std::string& url);

	/**
	 * Instantiate an Interpeter as a copy of another.
	 * @param other The other interpreter.
	 */
	static Interpreter fromClone(const Interpreter& other);

	/**
	 * See PIMPL_OPERATORS macro in Common.h
	 */
	PIMPL_OPERATORS(Interpreter);

	/**
	 * Advance the state-machine by a single microstep and return.
	 *
	 * This is the central function to drive the state machine. Calling step()
	 * will perform one *microstep* and return the current state of the
	 * interpreter. Here, the state is not to be confused with the interpreter's
	 * configuration.
	 *
	 * \snippet test-snippets.cpp Performing a microstep
	 *
	 * @param blockMs The maximum duration in milli-seconds to wait for an event to become available.
	 * @return The new state of the interpreter object.
	 */
	InterpreterState step(size_t blockMs = std::numeric_limits<size_t>::max());

	/**
	 * Unblock and mark for finalize.
	 */
	void cancel();

	/**
	 * Finalize and reset interpeter.
	 */
	void reset();

	/**
	 * Get all state elements that constitute the active configuration.
	 * @return A list of XML elements of the active states.
	 */
	std::list<XERCESC_NS::DOMElement*> getConfiguration();

	/**
	 * Determine whether the state with the given `id` is in the active configuration.
	 * @param id An identifier for a state from the SCXML document.
	 * @return Whether the interpreter is in state `id`.
	 */
	bool isInState(const std::string& stateId);

	/**
	 * The current state of the interpreter, not to be confused with its configuration.
	 * @return The current state of the interpreter object.
	 */
	InterpreterState getState();

	/**
	 * Return a list of possible syntactic and semantic issues with the interpreter's state-chart.
	 * @return A list of InterpreterIssue%s
	 */
	std::list<InterpreterIssue> validate();

	/**
	 * Enqueue an event to the interpreter's external queue.
	 * @event An event to be enqueued
	 */
	void receive(const Event& event);

	/**
	 * Adapt the constituting components for a SCXML interpreter.
	 */
	void setActionLanguage(ActionLanguage actionLanguage);

	/**
	 * Provide a custom Factory to instantiate dynamic instances for this and invoked state-chart instances.
	 */
	void setFactory(Factory* factory);

	/**
	 * Attach a monitor to make more details of the interpreter observable.
	 */
	void addMonitor(InterpreterMonitor* monitor);

	/**
	 * Remove a monitor that was attached previously.
	 */
	void removeMonitor(InterpreterMonitor* monitor);

	/**
	 * Return the logger associated with this interpreter
	 */
	Logger getLogger();

	/**
	 * Return the actual implementation of the Interperter.
	 */
	std::shared_ptr<InterpreterImpl> getImpl() const {
		return _impl;
	}

protected:
	std::shared_ptr<InterpreterImpl> _impl;

};

}

#endif /* end of include guard: INTERPRETER_H_6CD5A168 */
