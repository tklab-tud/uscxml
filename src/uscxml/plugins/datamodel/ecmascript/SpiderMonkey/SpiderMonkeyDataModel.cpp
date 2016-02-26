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

#include "uscxml/Common.h"
#include "uscxml/config.h"
#include "SpiderMonkeyDataModel.h"

#include "uscxml/Message.h"
#include "uscxml/dom/DOMUtils.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new SpiderMonkeyDataModelProvider() );
	return true;
}
#endif

static JSClass global_class = { "global",
                                JSCLASS_NEW_RESOLVE | JSCLASS_GLOBAL_FLAGS,
                                JS_PropertyStub,
                                JS_PropertyStub,
                                JS_PropertyStub,
                                JS_PropertyStub,
                                JS_EnumerateStub,
                                JS_ResolveStub,
                                JS_ConvertStub,
                                nullptr,
                                JSCLASS_NO_OPTIONAL_MEMBERS
                              };


JSRuntime* SpiderMonkeyDataModel::_jsRuntime = NULL;

SpiderMonkeyDataModel::SpiderMonkeyDataModel() {
	_jsCtx = NULL;
}

SpiderMonkeyDataModel::~SpiderMonkeyDataModel() {
	if (_jsCtx)
		JS_DestroyContext(_jsCtx);
}

void SpiderMonkeyDataModel::reportError(JSContext *cx, const char *message, JSErrorReport *report) {
#if 0
	struct JSErrorReport {
		const char      *filename;      /* source file name, URL, etc., or null */
		uintN           lineno;         /* source line number */
		const char      *linebuf;       /* offending source line without final \n */
		const char      *tokenptr;      /* pointer to error token in linebuf */
		const jschar    *uclinebuf;     /* unicode (original) line buffer */
		const jschar    *uctokenptr;    /* unicode (original) token pointer */
		uintN           flags;          /* error/warning, etc. */
		uintN           errorNumber;    /* the error number, e.g. see js.msg */
		const jschar    *ucmessage;     /* the (default) error message */
		const jschar    **messageArgs;  /* arguments for the error message */
	};
	exceptionEvent.data.compound["stacktrace"] = Data(stackTrace, Data::VERBATIM);
#endif

	Event exceptionEvent;
	exceptionEvent.name = "error.execution";
	exceptionEvent.eventType = Event::PLATFORM;

	exceptionEvent.data.compound["cause"] = Data(message, Data::VERBATIM);;
	exceptionEvent.data.compound["filename"] = Data(report->filename, Data::VERBATIM);
	exceptionEvent.data.compound["sourceline"] = Data(report->linebuf, Data::VERBATIM);
	exceptionEvent.data.compound["linenumber"] = Data(report->lineno, Data::INTERPRETED);

	std::stringstream ssUnderline;
	for (int i = 0; i < (report->tokenptr - report->linebuf); i++)
		ssUnderline << " ";
	ssUnderline << "^";

	exceptionEvent.data.compound["sourcemark"] = Data(ssUnderline.str(), Data::VERBATIM);
	throw exceptionEvent;
}

boost::shared_ptr<DataModelImpl> SpiderMonkeyDataModel::create(InterpreterImpl* interpreter) {
	if (_jsRuntime == NULL) {
		JSRuntime *rt = JS_NewRuntime(8L * 1024L * 1024L);
		if (!rt) {
			throw std::bad_alloc();
		}
	}

	boost::shared_ptr<SpiderMonkeyDataModel> dm = boost::shared_ptr<SpiderMonkeyDataModel>(new SpiderMonkeyDataModel());
	dm->_interpreter = interpreter;
	dm->_jsCtx = JS_NewContext(_jsRuntime, 8192);
	if (!dm->_jsCtx) {
		throw std::bad_alloc();
	}
	JS_SetOptions(dm->_jsCtx, JSOPTION_VAROBJFIX);
	JS_SetErrorReporter(dm->_jsCtx, reportError);

	dm->_global = JS_NewObject(dm->_jsCtx, &global_class, nullptr, nullptr);
	if (!JS_InitStandardClasses(dm->_jsCtx, dm->_global)) {
		throw std::bad_alloc();
	}

	return dm;
}

void SpiderMonkeyDataModel::pushContext() {
}

void SpiderMonkeyDataModel::popContext() {
}

void SpiderMonkeyDataModel::initialize() {
}

void SpiderMonkeyDataModel::setEvent(const Event& event) {
}

Data SpiderMonkeyDataModel::getStringAsData(const std::string& content) {
	Data data;
	return data;
}


bool SpiderMonkeyDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

bool SpiderMonkeyDataModel::isLocation(const std::string& expr) {
	return true;
}

uint32_t SpiderMonkeyDataModel::getLength(const std::string& expr) {
	return 0;
}

void SpiderMonkeyDataModel::setForeach(const std::string& item,
                                       const std::string& array,
                                       const std::string& index,
                                       uint32_t iteration) {
}

void SpiderMonkeyDataModel::eval(const Element<std::string>& scriptElem,
                                 const std::string& expr) {
}

bool SpiderMonkeyDataModel::isDeclared(const std::string& expr) {
	return true;
}

bool SpiderMonkeyDataModel::evalAsBool(const std::string& expr) {
	return evalAsBool(Arabica::DOM::Element<std::string>(), expr);
}

bool SpiderMonkeyDataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
}

std::string SpiderMonkeyDataModel::evalAsString(const std::string& expr) {
	return "";
}

double SpiderMonkeyDataModel::evalAsNumber(const std::string& expr) {
	return 0;
}

void SpiderMonkeyDataModel::assign(const Element<std::string>& assignElem,
                                   const Node<std::string>& node,
                                   const std::string& content) {
}

void SpiderMonkeyDataModel::assign(const std::string& location,
                                   const Data& data) {
}

void SpiderMonkeyDataModel::init(const Element<std::string>& dataElem,
                                 const Node<std::string>& doc,
                                 const std::string& content) {
};

void SpiderMonkeyDataModel::init(const std::string& location,
                                 const Data& data) {
}

std::string SpiderMonkeyDataModel::andExpressions(std::list<std::string> expressions) {
	if (expressions.size() == 0)
		return "";

	if (expressions.size() == 1)
		return *(expressions.begin());

	std::ostringstream exprSS;
	exprSS << "(";
	std::string conjunction = "";
	for (std::list<std::string>::const_iterator exprIter = expressions.begin();
	        exprIter != expressions.end();
	        exprIter++) {
		exprSS << conjunction << "(" << *exprIter << ")";
		conjunction = " && ";
	}
	exprSS << ")";
	return exprSS.str();
}

}