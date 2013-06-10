#ifndef FFMPEGINVOKER_H_VQD1V1C2
#define FFMPEGINVOKER_H_VQD1V1C2

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class FFMPEGInvoker : public InvokerImpl {
public:
	FFMPEGInvoker();
	virtual ~FFMPEGInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("ffmpeg");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#ffmpeg");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FFMPEGInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: FFMPEGINVOKER_H_VQD1V1C2 */
