#ifndef CONTIKI_CALC_INVOKER_H
#define CONTIKI_CALC_INVOKER_H
 
#include "uscxml/config.h"
#include "uscxml/plugins/InvokerImpl.h"
 
#ifdef __cplusplus
 #define EXTERNC extern "C"
#else
 #define EXTERNC 
#endif
#ifdef WITH_CONTIKI_CALC_EXAMPLE_INVOKER
EXTERNC{
#include "calc.h"
}
#endif // WITH_CONTIKI_CALC_EXAMPLE_INVOKER

namespace uscxml {
	class contiki_calc_Invoker : public InvokerImpl {
	public:
		contiki_calc_Invoker();
		virtual ~contiki_calc_Invoker();
		virtual std::shared_ptr<InvokerImpl> create(uscxml::InvokerCallbacks* callbacks);
		virtual std::list<std::string> getNames() {
			std::list<std::string> names;
			names.push_back("uscxml_contiki/calc");
			names.push_back("contiki/calc");
			names.push_back("contiki_calc");
			return names;
		}
		virtual Data getDataModelVariables();
		virtual void eventFromSCXML(const Event& event);
		virtual void invoke(const std::string& source, const Event& invokeEvent);
		virtual void uninvoke();
	};
}
#endif /* end of include guard: CONTIKI_CALC_INVOKER_H*/
