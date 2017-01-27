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

#ifndef V8DATAMODEL_H_KN8TWG0V
#define V8DATAMODEL_H_KN8TWG0V

#include "uscxml/config.h"
#include "uscxml/plugins/DataModelImpl.h"

#include <list>
#include <set>
#include <v8.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {
class Event;
class Data;
}

namespace uscxml {

/**
 * @ingroup datamodel
 * ECMAScript data-model via Google's V8.
 */

class V8DataModel : public DataModelImpl {
public:
	V8DataModel();
	virtual ~V8DataModel();
	virtual std::shared_ptr<DataModelImpl> create(DataModelCallbacks* callbacks);

	virtual void addExtension(DataModelExtension* ext);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("ecmascript");
		return names;
	}

	virtual bool isValidSyntax(const std::string& expr);

	virtual void setEvent(const Event& event);

	// foreach
	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual bool evalAsBool(const std::string& expr);
	virtual Data evalAsData(const std::string& expr);
	virtual Data getAsData(const std::string& content);

	virtual bool isDeclared(const std::string& expr);

	virtual void assign(const std::string& location,
	                    const Data& data,
	                    const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());
	virtual void init(const std::string& location,
	                  const Data& data,
	                  const std::map<std::string, std::string>& attr = std::map<std::string, std::string>());

protected:

	static void jsExtension(const v8::FunctionCallbackInfo<v8::Value>& info);
	static void jsIn(const v8::FunctionCallbackInfo<v8::Value>& info);
	static void jsPrint(const v8::FunctionCallbackInfo<v8::Value>& info);

	//v8::Local<v8::Object> _event; // Persistent events leak ..
	v8::Persistent<v8::Context> _context;
	static v8::Isolate* _isolate;

	v8::Persistent<v8::Object> _ioProcessors;
	v8::Persistent<v8::Object> _invokers;

	static void getIOProcessors(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info);
	static void getInvokers(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info);
	static void getAttribute(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info);
	static void setWithException(v8::Local<v8::String> property,
	                             v8::Local<v8::Value> value,
	                             const v8::PropertyCallbackInfo<void>& info);

	v8::Local<v8::Value> evalAsValue(const std::string& expr, bool dontThrow = false);
	v8::Local<v8::Value> getDataAsValue(const Data& data);
	Data getValueAsData(const v8::Local<v8::Value>& value);
	v8::Local<v8::Value> getNodeAsValue(const XERCESC_NS::DOMNode* node);
	void throwExceptionEvent(const v8::TryCatch& tryCatch);

	std::set<DataModelExtension*> _extensions;

private:
	Data getValueAsData(const v8::Local<v8::Value>& value, std::set<v8::Value*>& alreadySeen);

	static std::mutex _initMutex;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(V8DataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: V8DATAMODEL_H_KN8TWG0V */
