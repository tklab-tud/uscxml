#include "contiki_ftp_Invoker.h" 
#include "iostream"
 
namespace uscxml {
 
contiki_ftp_Invoker::contiki_ftp_Invoker() {}
contiki_ftp_Invoker::~contiki_ftp_Invoker() {}
std::shared_ptr<InvokerImpl> contiki_ftp_Invoker::create(uscxml::InvokerCallbacks* callbacks) {
	std::shared_ptr<contiki_ftp_Invoker> invoker(new contiki_ftp_Invoker());
	invoker->_callbacks = callbacks;
	return invoker;
}
 
Data contiki_ftp_Invoker::getDataModelVariables() {
	Data data;
	return data;
}
 
void contiki_ftp_Invoker::eventFromSCXML(const Event& event) {}
void contiki_ftp_Invoker::invoke(const std::string& source, const Event& invokeEvent) {
	process_start(&ftp_process, NULL);
}
 
void contiki_ftp_Invoker::uninvoke() {	
	if (process_is_running(&ftp_process))
	 	process_exit(&ftp_process);
	}
}

