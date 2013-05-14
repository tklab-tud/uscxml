#ifndef MMIIOPROCESSOR_H_W09J90F0
#define MMIIOPROCESSOR_H_W09J90F0

#include "MMIMessages.h"

namespace uscxml {

class MMIComponent {
public:
	MMIComponent();
	virtual ~MMIComponent();

	/** Modality component */
	virtual PrepareResponse prepare(const PrepareRequest&) = 0;
	virtual StartResponse start(const StartRequest&) = 0;
	virtual CancelResponse cancel(const CancelRequest&) = 0;
	virtual PauseResponse pause(const PauseRequest&) = 0;
	virtual ResumeResponse resume(const ResumeRequest&) = 0;
	virtual ExtensionNotification extension(const ExtensionNotification&) = 0;
	virtual ClearContextRequest clearContext(const ClearContextRequest&) = 0;
	virtual StatusResponse status(const StatusRequest&) = 0;

	/** Interaction Manager */
	virtual NewContextResponse newContext(const NewContextRequest&) = 0;
	virtual DoneNotification done(const DoneNotification&) = 0;
//	virtual ExtensionNotification extension(const ExtensionNotification&);


};

}


#endif /* end of include guard: MMIIOPROCESSOR_H_W09J90F0 */
