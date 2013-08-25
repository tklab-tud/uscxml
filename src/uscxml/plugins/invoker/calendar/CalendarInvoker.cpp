#include "CalendarInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new CalendarInvokerProvider() );
	return true;
}
#endif

CalendarInvoker::CalendarInvoker() {
	_icalSet = NULL;
	_icalComp = NULL;
}

CalendarInvoker::~CalendarInvoker() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	std::set<std::string>::iterator _eventIdIter = _eventIds.begin();
	while(_eventIdIter != _eventIds.end()) {
		_interpreter->getDelayQueue()->cancelEvent(*_eventIdIter);
		_eventIds.erase(_eventIdIter++);

	}

	std::map<std::string, CalendarEvent*>::iterator eventIter = _events.begin();
	while(eventIter != _events.end()) {
		delete eventIter->second;
		eventIter++;
	}

	if (_icalComp)
		icalcomponent_free(_icalComp);
};

boost::shared_ptr<InvokerImpl> CalendarInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<CalendarInvoker> invoker = boost::shared_ptr<CalendarInvoker>(new CalendarInvoker());
	invoker->_interpreter = interpreter;

	icalerror_set_error_state(ICAL_PARSE_ERROR, ICAL_ERROR_NONFATAL);

//	invoker->_calFile = URL::tmpFile();
//	invoker->_icalSet = icalfileset_new(invoker->_calFile.c_str());

//	if (!invoker->_icalSet) {
//		LOG(WARNING) << "Could not create new ical fileset: " << icalerror_perror();
//	}

	return invoker;
}

Data CalendarInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void CalendarInvoker::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
}

void CalendarInvoker::cancel(const std::string sendId) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	std::set<std::string>::iterator _eventIdIter = _eventIds.begin();
	while(_eventIdIter != _eventIds.end()) {
		_interpreter->getDelayQueue()->cancelEvent(*_eventIdIter);
		_eventIds.erase(_eventIdIter++);
	}
}

void CalendarInvoker::invoke(const InvokeRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	_icalComp = addIcal(req.content);
//	dumpComponent(_icalComp);
	setupEvents(_icalComp);

}

icalcomponent* CalendarInvoker::addIcal(const std::string& icalString) {

	icalcomponent* root = icalparser_parse_string(icalString.c_str());
	if (!root) {
		LOG(WARNING) << "Could not parse ical data: " << icalerror_perror();
		return NULL;
	}
//	icalerrorenum err;
//	err = icalset_add_component(_icalSet, root);
//	icalfileset_commit(_icalSet);

	return root;
}

void CalendarInvoker::setupEvents(icalcomponent* comp) {
//	dumpComponent(comp);

	switch (icalcomponent_isa(comp)) {
	case ICAL_VCALENDAR_COMPONENT:
	case ICAL_XROOT_COMPONENT:
		break;
	case ICAL_VALARM_COMPONENT: {
		break;
	}
	case ICAL_VEVENT_COMPONENT: {
		// event to map
		CalendarEvent* event = new CalendarEvent(comp);
		_events[toStr((uintptr_t)event)] = event;
		queueEvent(event);
		break;
	}
	default:
//			dumpComponent(comp);
		break;
	}

	icalcomponent* child = icalcomponent_get_first_component(comp, ICAL_ANY_COMPONENT);
	while(child) {
		setupEvents(child);
		child = icalcomponent_get_next_component(comp, ICAL_ANY_COMPONENT);
	}

}

void CalendarInvoker::queueEvent(CalendarEvent* event) {
	if (_events.find(toStr((uintptr_t)event)) == _events.end()) {
		_events[toStr((uintptr_t)event)] = event;
	}
	time_t now = time(NULL);
	struct icaltime_span span;

	if (event->_nextSpan.start > 0) {
		span = event->getNextDuration(event->_nextSpan.start + 1);
	} else {
		span = event->getNextDuration(now);
	}

#if 0
	if (span.end > 0) {
		std::cout << "\t\t" << ctime(&span.start);
		std::cout << "\t\t" << ctime(&span.end);
		span = event->getNextDuration(span.end);
	}
#endif

	if (span.start <= 0 || span.end <= 0) {
		event->_nextSpan.start = 0;
		event->_nextSpan.end = 0;
		return;
	}

	int beginSecs = span.start - now;
	int endSecs = span.end - now;

	if (beginSecs > endSecs) {
		LOG(WARNING) << "Event ends before it starts";
		return;
	}

	event->_nextSpan = span;

	std::string beginEventId = event->getId() + "." + toStr(span.start) + ".started";
	std::string endEventId = event->getId() + "." + toStr(span.end) + ".ended";

#if 0
	beginSecs = 1;
	endSecs = 2;
#endif
	if (beginSecs > 0) {
		_interpreter->getDelayQueue()->addEvent(beginEventId, CalendarInvoker::raiseEvent, beginSecs * 1000, this);
		_eventIds.insert(beginEventId);
	} else {
		raiseEvent(this, beginEventId);
	}
	_interpreter->getDelayQueue()->addEvent(endEventId, CalendarInvoker::raiseEvent, endSecs * 1000, this);
	_eventIds.insert(endEventId);

}

void CalendarInvoker::raiseEvent(void* userdata, const std::string eventId) {
	CalendarInvoker* INSTANCE = (CalendarInvoker*)userdata;
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);

	std::string address = eventId.substr(0, eventId.find_first_of("."));

	if (INSTANCE->_events.find(address) == INSTANCE->_events.end()) {
		LOG(WARNING) << "No such event: " << eventId;
		return;
	}

	if(INSTANCE->_eventIds.find(eventId) != INSTANCE->_eventIds.end()) {
		INSTANCE->_eventIds.erase(eventId);
	}

	CalendarEvent* calEvent = INSTANCE->_events[address];
	Event event;

	event.data = *calEvent;
	if (boost::ends_with(eventId, ".started")) {
		event.name = "event.started." + calEvent->getId();
		assert(!calEvent->_active);
		calEvent->_active = true;
	} else {
		event.name = "event.ended." + calEvent->getId();
		assert(calEvent->_active);
		calEvent->_active = false;
	}
	INSTANCE->returnEvent(event);

	// event ended, reschedule next event
	if (boost::ends_with(eventId, ".ended"))
		INSTANCE->queueEvent(calEvent);
}

/**
 * Get the next duration for this event starting no earlier
 * than the given time.
 */
icaltime_span CalendarEvent::getNextDuration(time_t time) {
	if (!_icalComp)
		return icaltime_span_new(icaltime_null_time(), icaltime_null_time(), 0);

	// see icalcomponent_foreach_recurrence
	icalproperty *rrule;

	icaltimetype calTime = icaltime_from_timet_with_zone(time, 0, 0);

	// actual occurence, without reocurrence
	if (!icalproperty_recurrence_is_excluded(_icalComp, &_dtstart, &_dtend)) {
		if (icaltime_compare(_dtstart, calTime) >= 0) {
			// start is still in the future
			return icaltime_span_new(_dtstart, _dtend, 0);
		}
	}

	icaltime_span recDur = icaltime_span_new(icaltime_null_time(), icaltime_null_time(), 0);

	// iterate all rrules
	for (rrule = icalcomponent_get_first_property(_icalComp, ICAL_RRULE_PROPERTY);
	        rrule != NULL;
	        rrule = icalcomponent_get_next_property(_icalComp, ICAL_RRULE_PROPERTY)) {

		struct icalrecurrencetype recurType = icalproperty_get_rrule(rrule);
		icalrecur_iterator *ritr;
		struct icaltimetype rtime;

		// do we have an old iterator that has not yet passed time?
		if (_recIters.find(rrule) != _recIters.end()) {
			if (_recIters[rrule].second > time) {
				icalrecur_iterator_free(_recIters[rrule].first);
				_recIters[rrule].first = icalrecur_iterator_new(recurType, _dtstart);

				// skip initial non-reoccurence
				if(_recIters[rrule].first)
					rtime = icalrecur_iterator_next(_recIters[rrule].first);

			}
			ritr  = _recIters[rrule].first;
		} else {
			// create a new iterator for this rrule
			_recIters[rrule] = std::make_pair(icalrecur_iterator_new(recurType, _dtstart), 0);
			ritr  = _recIters[rrule].first;
		}

//		std::cout << icalrecurrencetype_as_string(&recurType) << std::endl;

		while (ritr) {
			rtime = icalrecur_iterator_next(ritr);

#if 0
			time_t tt = icaltime_as_timet(rtime);
			std::cout << "\t\t" << ctime(&tt);
#endif

			if (icaltime_is_null_time(rtime)) {
				// remove iterator
				icalrecur_iterator_free(_recIters[rrule].first);
				_recIters.erase(rrule);
				break; // for next rule
			}
			_recIters[rrule].second = icaltime_as_timet(rtime);

			if (icaltime_compare(rtime, calTime) < 0)
				continue; // until we are after given time

			if (icalproperty_recurrence_is_excluded(_icalComp, &_dtstart, &rtime))
				continue;

			icaltime_span thisDur = icaltime_span_new(rtime, rtime, 1);
			thisDur.end += _dtduration;

			if (recDur.start == 0 || thisDur.start < recDur.start) {
				// update soonest reoccurence with the one from this rule
				recDur = thisDur;
			}
			break; // we are after the event
		}
	}
	return recDur;
}

CalendarEvent::~CalendarEvent() {
	std::map<icalproperty*, std::pair<icalrecur_iterator*, time_t> >::iterator recItersIter = _recIters.begin();
	while(recItersIter != _recIters.end()) {
		icalrecur_iterator_free(recItersIter->second.first);
		recItersIter++;
	}
}

CalendarEvent::CalendarEvent(icalcomponent* icalComp) {
	_nextSpan.start = 0;
	_nextSpan.end = 0;
	_icalComp = NULL;
	_active = false;


	_dtstart = icalcomponent_get_dtstart(icalComp);
	_dtend = icalcomponent_get_dtend(icalComp);

	if (!icaltime_is_valid_time(_dtstart)) {
		LOG(WARNING) << "Start of event not a valid time";
		return;
	}

	if (!icaltime_is_valid_time(_dtend)) {
		LOG(WARNING) << "End of event not a valid time";
		return;
	}

	_dtduration = icaldurationtype_as_int(icaltime_subtract(_dtend, _dtstart));

	if (_dtduration <= 0) {
		LOG(WARNING) << "Event has negative or zero duration";
		return;
	}

	_icalComp = icalComp;

	// initialize all iterators - not really needed anymore
	for (icalproperty* rrule = icalcomponent_get_first_property(_icalComp, ICAL_RRULE_PROPERTY);
	        rrule != NULL;
	        rrule = icalcomponent_get_next_property(_icalComp, ICAL_RRULE_PROPERTY)) {

		struct icalrecurrencetype recurType = icalproperty_get_rrule(rrule);
		icalrecur_iterator *ritr  = icalrecur_iterator_new(recurType, _dtstart);

		_recIters[rrule] = std::make_pair(ritr, 0);
	}


}

CalendarEvent::operator Data() {
	Data data;
	data = CalendarInvoker::toData(_icalComp);
	return data;
}

Data CalendarInvoker::toData(icalcomponent* comp) {
	Data data;
	data.compound["kind"] = Data(icalcomponent_kind_to_string(icalcomponent_isa(comp)), Data::VERBATIM);

	// iterate all properties
	icalproperty* prop = icalcomponent_get_first_property(comp, ICAL_ANY_PROPERTY);
	while(prop) {
		std::string propName = icalproperty_kind_to_string(icalproperty_isa(prop));
		boost::to_lower(propName);

#if 0
		// iterate all parameters
		icalparameter* para = icalproperty_get_first_parameter(prop, ICAL_ANY_PARAMETER);
		while(para) {
			std::string paraName = icalparameter_kind_to_string(icalparameter_isa(para));

			switch(icalparameter_get_value(para)) {
			case ICAL_VALUE_X:
				data.compound[propName].compound[paraName] = Data(icalparameter_get_x(para), Data::VERBATIM);
				break;
			case ICAL_VALUE_BOOLEAN:
			case ICAL_VALUE_BINARY:
			case ICAL_VALUE_DATE:
			case ICAL_VALUE_DURATION:
			case ICAL_VALUE_FLOAT:
			case ICAL_VALUE_INTEGER:
			case ICAL_VALUE_PERIOD:
			case ICAL_VALUE_RECUR:
			case ICAL_VALUE_TEXT:
			case ICAL_VALUE_URI:
			case ICAL_VALUE_ERROR:
			case ICAL_VALUE_DATETIME:
			case ICAL_VALUE_UTCOFFSET:
			case ICAL_VALUE_CALADDRESS:
			case ICAL_VALUE_NONE:
				data.compound[propName].compound[paraName] = Data("", Data::VERBATIM);
				break;
			}

			para = icalproperty_get_next_parameter(prop, ICAL_ANY_PARAMETER);
		}
		data.compound[propName].compound["value"] = Data(icalproperty_get_value_as_string(prop), Data::VERBATIM);
#endif
#if 0
		data.compound[propName] = Data(icalproperty_as_ical_string(prop), Data::VERBATIM);
#endif
		data.compound[propName] = Data(icalproperty_get_value_as_string(prop), Data::VERBATIM);

		prop = icalcomponent_get_next_property(comp, ICAL_ANY_PROPERTY);
	}


	icalcomponent* child = icalcomponent_get_first_component(comp, ICAL_ANY_COMPONENT);
	while(child) {
		data.compound["childs"].array.push_back(toData(child));
		child = icalcomponent_get_next_component(comp, ICAL_ANY_COMPONENT);
	}

	return data;
}

#if 0
void CalendarInvoker::dumpComponent(icalcomponent* comp) {
	std::cout << icalcomponent_kind_to_string(icalcomponent_isa(comp)) << std::endl;

	struct icaltimetype start, end;
	time_t tt;

	icalproperty *startProp = icalcomponent_get_first_property(comp, ICAL_DTSTART_PROPERTY);
	if (startProp) {
		start = icalproperty_get_dtstart(startProp);
	}

	icalproperty *endProp = icalcomponent_get_first_property(comp, ICAL_DTEND_PROPERTY);
	if (endProp) {
		end = icalproperty_get_dtend(endProp);
	}

	icalproperty *prop = icalcomponent_get_first_property(comp, ICAL_ANY_PROPERTY);

	while(prop) {
		std::cout << "\t" << icalproperty_kind_to_string(icalproperty_isa(prop)) << std::endl;
		switch (icalproperty_isa(prop)) {
		case ICAL_ANY_PROPERTY:
		case ICAL_ACKNOWLEDGED_PROPERTY:
		case ICAL_ACTION_PROPERTY:
		case ICAL_ALLOWCONFLICT_PROPERTY:
		case ICAL_ATTACH_PROPERTY:
		case ICAL_ATTENDEE_PROPERTY:
		case ICAL_CALID_PROPERTY:
		case ICAL_CALMASTER_PROPERTY:
		case ICAL_CALSCALE_PROPERTY:
		case ICAL_CAPVERSION_PROPERTY:
		case ICAL_CARLEVEL_PROPERTY:
		case ICAL_CARID_PROPERTY:
		case ICAL_CATEGORIES_PROPERTY:
		case ICAL_CLASS_PROPERTY:
		case ICAL_CMD_PROPERTY:
		case ICAL_COMMENT_PROPERTY:
		case ICAL_COMPLETED_PROPERTY:
		case ICAL_COMPONENTS_PROPERTY:
		case ICAL_CONTACT_PROPERTY:
		case ICAL_CREATED_PROPERTY:
		case ICAL_CSID_PROPERTY:
		case ICAL_DATEMAX_PROPERTY:
		case ICAL_DATEMIN_PROPERTY:
		case ICAL_DECREED_PROPERTY:
		case ICAL_DEFAULTCHARSET_PROPERTY:
		case ICAL_DEFAULTLOCALE_PROPERTY:
		case ICAL_DEFAULTTZID_PROPERTY:
		case ICAL_DEFAULTVCARS_PROPERTY:
		case ICAL_DENY_PROPERTY:
			break;
		case ICAL_DESCRIPTION_PROPERTY:
			std::cout << "\t\t" << icalproperty_get_description(prop) << std::endl;
			break;
		case ICAL_DTEND_PROPERTY: {
			end = icalproperty_get_dtend(prop);
			tt = icaltime_as_timet(start);
			std::cout << "\t\t" << ctime(&tt) << std::endl;
			break;
		}
		case ICAL_DTSTAMP_PROPERTY:
			break;
		case ICAL_DTSTART_PROPERTY: {
			start = icalproperty_get_dtstart(prop);
			tt = icaltime_as_timet(start);
			std::cout << "\t\t" << ctime(&tt) << std::endl;
			break;
		}
		case ICAL_DUE_PROPERTY:
		case ICAL_DURATION_PROPERTY:
		case ICAL_EXDATE_PROPERTY:
		case ICAL_EXPAND_PROPERTY:
		case ICAL_EXRULE_PROPERTY:
		case ICAL_FREEBUSY_PROPERTY:
		case ICAL_GEO_PROPERTY:
		case ICAL_GRANT_PROPERTY:
		case ICAL_ITIPVERSION_PROPERTY:
		case ICAL_LASTMODIFIED_PROPERTY:
		case ICAL_LOCATION_PROPERTY:
		case ICAL_MAXCOMPONENTSIZE_PROPERTY:
		case ICAL_MAXDATE_PROPERTY:
		case ICAL_MAXRESULTS_PROPERTY:
		case ICAL_MAXRESULTSSIZE_PROPERTY:
		case ICAL_METHOD_PROPERTY:
		case ICAL_MINDATE_PROPERTY:
		case ICAL_MULTIPART_PROPERTY:
		case ICAL_NAME_PROPERTY:
		case ICAL_ORGANIZER_PROPERTY:
		case ICAL_OWNER_PROPERTY:
		case ICAL_PERCENTCOMPLETE_PROPERTY:
		case ICAL_PERMISSION_PROPERTY:
		case ICAL_PRIORITY_PROPERTY:
		case ICAL_PRODID_PROPERTY:
		case ICAL_QUERY_PROPERTY:
		case ICAL_QUERYLEVEL_PROPERTY:
		case ICAL_QUERYID_PROPERTY:
		case ICAL_QUERYNAME_PROPERTY:
		case ICAL_RDATE_PROPERTY:
		case ICAL_RECURACCEPTED_PROPERTY:
		case ICAL_RECUREXPAND_PROPERTY:
		case ICAL_RECURLIMIT_PROPERTY:
		case ICAL_RECURRENCEID_PROPERTY:
		case ICAL_RELATEDTO_PROPERTY:
		case ICAL_RELCALID_PROPERTY:
		case ICAL_REPEAT_PROPERTY:
		case ICAL_REQUESTSTATUS_PROPERTY:
		case ICAL_RESOURCES_PROPERTY:
		case ICAL_RESTRICTION_PROPERTY:
			break;
		case ICAL_RRULE_PROPERTY: {
			//				struct icaltimetype start = icaltime_from_timet(1,0);
			//				struct icaltimetype start = icalproperty_get_dtstart(icalcomponent_get_first_property(comp,ICAL_DTSTART_PROPERTY));

			//				struct icaltimetype end = icaltime_today();
			struct icalrecurrencetype recur = icalproperty_get_rrule(prop);
			struct icaltimetype next;

			icalrecur_iterator* ritr;
			for(ritr = icalrecur_iterator_new(recur,start),
			        next = icalrecur_iterator_next(ritr);
			        !icaltime_is_null_time(next);
			        next = icalrecur_iterator_next(ritr)) {

				tt = icaltime_as_timet(next);
				printf("  %s",ctime(&tt ));

			}
			icalrecur_iterator_free(ritr);

			break;
		}
		case ICAL_SCOPE_PROPERTY:
		case ICAL_SEQUENCE_PROPERTY:
		case ICAL_STATUS_PROPERTY:
		case ICAL_STORESEXPANDED_PROPERTY:
		case ICAL_SUMMARY_PROPERTY:
		case ICAL_TARGET_PROPERTY:
		case ICAL_TRANSP_PROPERTY:
		case ICAL_TRIGGER_PROPERTY:
		case ICAL_TZID_PROPERTY:
		case ICAL_TZNAME_PROPERTY:
		case ICAL_TZOFFSETFROM_PROPERTY:
		case ICAL_TZOFFSETTO_PROPERTY:
		case ICAL_TZURL_PROPERTY:
		case ICAL_UID_PROPERTY:
		case ICAL_URL_PROPERTY:
		case ICAL_VERSION_PROPERTY:
		case ICAL_X_PROPERTY:
		case ICAL_XLICCLASS_PROPERTY:
		case ICAL_XLICCLUSTERCOUNT_PROPERTY:
		case ICAL_XLICERROR_PROPERTY:
		case ICAL_XLICMIMECHARSET_PROPERTY:
		case ICAL_XLICMIMECID_PROPERTY:
		case ICAL_XLICMIMECONTENTTYPE_PROPERTY:
		case ICAL_XLICMIMEENCODING_PROPERTY:
		case ICAL_XLICMIMEFILENAME_PROPERTY:
		case ICAL_XLICMIMEOPTINFO_PROPERTY:
		case ICAL_NO_PROPERTY:
			break;
		}
		prop = icalcomponent_get_next_property(comp, ICAL_ANY_PROPERTY);
	}

	switch (icalcomponent_isa(comp)) {
	case ICAL_NO_COMPONENT:
	case ICAL_ANY_COMPONENT:
		break;
	case ICAL_XROOT_COMPONENT: {
		icalcomponent* child = icalcomponent_get_first_component(comp, ICAL_ANY_COMPONENT);
		while(child) {
			dumpComponent(child);
			child = icalcomponent_get_next_component(comp, ICAL_ANY_COMPONENT);
		}
		break;
	}
	case ICAL_XATTACH_COMPONENT:
	case ICAL_VEVENT_COMPONENT:
	case ICAL_VTODO_COMPONENT:
	case ICAL_VJOURNAL_COMPONENT:
	case ICAL_VCALENDAR_COMPONENT:
	case ICAL_VAGENDA_COMPONENT:
	case ICAL_VFREEBUSY_COMPONENT:
	case ICAL_VALARM_COMPONENT:
	case ICAL_XAUDIOALARM_COMPONENT:
	case ICAL_XDISPLAYALARM_COMPONENT:
	case ICAL_XEMAILALARM_COMPONENT:
	case ICAL_XPROCEDUREALARM_COMPONENT:
	case ICAL_VTIMEZONE_COMPONENT:
	case ICAL_XSTANDARD_COMPONENT:
	case ICAL_XDAYLIGHT_COMPONENT:
	case ICAL_X_COMPONENT:
	case ICAL_VSCHEDULE_COMPONENT:
	case ICAL_VQUERY_COMPONENT:
	case ICAL_VREPLY_COMPONENT:
	case ICAL_VCAR_COMPONENT:
	case ICAL_VCOMMAND_COMPONENT:
	case ICAL_XLICINVALID_COMPONENT:
	case ICAL_XLICMIMEPART_COMPONENT:
		break;
	}
}
#endif

}