
#include "contiki_calc_Invoker.h" 
EXTERNC{
#include "invokers/calc.h"
}
//#define WITH_CONTIKI_CALC_EXAMPLE_INVOKER
#include "iostream"
 
namespace uscxml {
 
contiki_calc_Invoker::contiki_calc_Invoker() {}
contiki_calc_Invoker::~contiki_calc_Invoker() {}
std::shared_ptr<InvokerImpl> contiki_calc_Invoker::create(uscxml::InvokerCallbacks* callbacks) {
	std::shared_ptr<contiki_calc_Invoker> invoker(new contiki_calc_Invoker());
	invoker->_callbacks = callbacks;
	return invoker;
}
 
Data contiki_calc_Invoker::getDataModelVariables() {
	Data data;
	return data;
}
 
void contiki_calc_Invoker::eventFromSCXML(const Event& event) {}
void contiki_calc_Invoker::invoke(const std::string& source, const Event& invokeEvent) {

	process_start(&calc_process, NULL);
}
 
void contiki_calc_Invoker::uninvoke() {	

	if (process_is_running(&calc_process))
	 	process_exit(&calc_process);
	}
}

