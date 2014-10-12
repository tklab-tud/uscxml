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

#ifndef SWIDATAMODEL_H_KN8TWG0V
#define SWIDATAMODEL_H_KN8TWG0V

#include "uscxml/Interpreter.h"
#include "uscxml/SWIConfig.h"

#include <list>
#include <SWI-cpp.h>


#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class SWIDataModel : public DataModelImpl {
public:
	class SWIEngineLock {
	public:
		SWIEngineLock() {
			isLocked = false;
			int rc = PL_set_engine(PL_ENGINE_MAIN, NULL);
			if (rc == PL_ENGINE_SET) {
				isLocked = true;
			}
		}
		~SWIEngineLock() {
			if (isLocked)
				PL_set_engine(NULL, NULL);
		}
		bool isLocked;
	};

	SWIDataModel();
	virtual ~SWIDataModel();
	virtual boost::shared_ptr<DataModelImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("prolog");
		return names;
	}

	virtual void initialize();
	virtual void setSessionId(const std::string& sessionId);
	virtual void setName(const std::string& name);
	virtual void setEvent(const Event& event);

	virtual void registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor);

	virtual bool validate(const std::string& location, const std::string& schema);
	virtual bool isLocation(const std::string& expr);

	virtual uint32_t getLength(const std::string& expr);
	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration);

	virtual void pushContext();
	virtual void popContext();

	virtual void assign(const Arabica::DOM::Element<std::string>& assignElem,
	                    const Arabica::DOM::Node<std::string>& node,
	                    const std::string& content);
	virtual void assign(const std::string& location, const Data& data);

	virtual void init(const Arabica::DOM::Element<std::string>& dataElem,
	                  const Arabica::DOM::Node<std::string>& node,
	                  const std::string& content);
	virtual void init(const std::string& location, const Data& data);

	virtual void eval(const Arabica::DOM::Element<std::string>& scriptElem,
	                  const std::string& expr);

	virtual bool isDeclared(const std::string& expr);

	virtual Data getStringAsData(const std::string& content);

	virtual std::string evalAsString(const std::string& expr);
	virtual bool evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr);
	virtual bool evalAsBool(const std::string& expr);

	static foreign_t inPredicate(term_t a0, int arity, void* context);
protected:
	void assertFromData(const Data& data, const std::string& expr, size_t nesting);

	static Data termAsData(PlTerm term);
	static PlTerm dataAsTerm(Data data);

//	virtual std::list<PlCompound> getSolutions(PlCompound compound);
	virtual std::map<std::string, PlTerm> resolveAtoms(PlTerm& term, PlTerm& orig);

	static int dictCallBack(term_t key, term_t value, int last, void *closure);

	static PL_blob_t blobType;
	static void acquireBlob(atom_t symbol);
	static int releaseBlob(atom_t symbol);
	static int compareBlob(atom_t a, atom_t b);
	static int writeBlob(void *s, atom_t symbol, int flags);

	Event _event;

	std::string _plModule;
	std::string _name;
	std::string _sessionId;
	PL_engine_t _engine;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(SWIDataModel, DataModelImpl);
#endif

}

#endif /* end of include guard: SWIDATAMODEL_H_KN8TWG0V */
