#ifndef CALENDARINVOKER_H_W09J90F0
#define CALENDARINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class CalendarInvoker : public InvokerImpl {
public:
	CalendarInvoker();
	virtual ~CalendarInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("calendar");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#calendar");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(CalendarInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: CALENDARINVOKER_H_W09J90F0 */
