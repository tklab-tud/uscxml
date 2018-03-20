#ifndef CONTIKI_FTP_INVOKER_H
#define CONTIKI_FTP_INVOKER_H
 
#include "uscxml/config.h"
#include "uscxml/plugins/InvokerImpl.h"
 
#ifdef __cplusplus
 #define EXTERNC extern "C"
#else
 #define EXTERNC 
#endif
 
EXTERNC{
#include "ftp.h"
}

namespace uscxml {
	class contiki_ftp_Invoker : public InvokerImpl {
	public:
		contiki_ftp_Invoker();
		virtual ~contiki_ftp_Invoker();
		virtual std::shared_ptr<InvokerImpl> create(uscxml::InvokerCallbacks* callbacks);
		virtual std::list<std::string> getNames() {
			std::list<std::string> names;
			names.push_back("uscxml_contiki/ftp");
			names.push_back("contiki/ftp");
			names.push_back("contiki_ftp");
			return names;
		}
		virtual Data getDataModelVariables();
		virtual void eventFromSCXML(const Event& event);
		virtual void invoke(const std::string& source, const Event& invokeEvent);
		virtual void uninvoke();
	};
}
#endif /* end of include guard: CONTIKI_FTP_INVOKER_H*/
