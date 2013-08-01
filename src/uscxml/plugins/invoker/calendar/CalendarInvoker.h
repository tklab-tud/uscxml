#ifndef CALENDARINVOKER_H_W09J90F0
#define CALENDARINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>
extern "C" {
#	include <libical/ical.h>
#	include <libical/icalss.h>
}

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class CalendarEvent {
public:
	CalendarEvent(icalcomponent* _icalComp);
	~CalendarEvent();
	icalcomponent* _icalComp;
	icaltime_span _nextSpan;
	bool _active;
	struct icaltimetype _dtstart, _dtend;
	time_t _dtduration;

	icaltime_span getNextDuration(time_t time);
	std::string getId() {
		return toStr((uintptr_t)this);
	}

	std::map<icalproperty*, std::pair<icalrecur_iterator*, time_t> > _recIters;
	operator Data();
};

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

	static void raiseEvent(void* userdata, const std::string eventId);
	static Data toData(icalcomponent* comp);
protected:
	icalcomponent* addIcal(const std::string& icalString);
	void setupEvents(icalcomponent* comp);
	void queueEvent(CalendarEvent* event);

	void dumpComponent(icalcomponent* comp);

	tthread::recursive_mutex _mutex;

	std::string _calFile;
	icalset* _icalSet;
	icalcomponent* _icalComp;

	std::set<std::string> _eventIds;
	std::map<std::string, CalendarEvent*> _events;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(CalendarInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: CALENDARINVOKER_H_W09J90F0 */
