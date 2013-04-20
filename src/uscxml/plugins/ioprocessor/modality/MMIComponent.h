#ifndef MMIIOPROCESSOR_H_W09J90F0
#define MMIIOPROCESSOR_H_W09J90F0

#include <uscxml/Interpreter.h>
#include "MMIMessages.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class MMIIOProcessor : public IOProcessorImpl {
public:
	MMIIOProcessor();
	virtual ~MMIIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		return std::set<std::string>();
	};

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);

	/** Modality component */
	virtual PrepareResponse prepare(const PrepareRequest&);
	virtual StartResponse start(const StartRequest&);
	virtual CancelResponse cancel(const CancelRequest&);
	virtual PauseResponse pause(const PauseRequest&);
	virtual ResumeResponse resume(const ResumeRequest&);
	virtual ExtensionNotification extension(const ExtensionNotification&);
	virtual ClearContextRequest clearContext(const ClearContextRequest&);
	virtual StatusResponse status(const StatusRequest&);

	/** Interaction Manager */
	virtual NewContextResponse newContext(const NewContextRequest&);
	virtual DoneNotification done(const DoneNotification&);
//	virtual ExtensionNotification extension(const ExtensionNotification&);


};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(MMIIOProcessor, IOProcessorImpl);
#endif

}


#endif /* end of include guard: MMIIOPROCESSOR_H_W09J90F0 */
