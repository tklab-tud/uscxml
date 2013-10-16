/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef MMIPROTOBRIDGE_H_T6VXUX69
#define MMIPROTOBRIDGE_H_T6VXUX69

#include "LifeCycleEvents.pb.h"
#include "StringDataExtension.pb.h"
#include "MMIMessages.h"

namespace uscxml {

class MMIProtoBridge {
public:
	static ::LifeCycleEvent toProto(const NewContextRequest&);
	static ::LifeCycleEvent toProto(const NewContextResponse&);
	static ::LifeCycleEvent toProto(const PrepareRequest&);
	static ::LifeCycleEvent toProto(const PrepareResponse&);
	static ::LifeCycleEvent toProto(const StartRequest&);
	static ::LifeCycleEvent toProto(const StartResponse&);
	static ::LifeCycleEvent toProto(const DoneNotification&);
	static ::LifeCycleEvent toProto(const CancelRequest&);
	static ::LifeCycleEvent toProto(const CancelResponse&);
	static ::LifeCycleEvent toProto(const PauseRequest&);
	static ::LifeCycleEvent toProto(const PauseResponse&);
	static ::LifeCycleEvent toProto(const ResumeRequest&);
	static ::LifeCycleEvent toProto(const ResumeResponse&);
	static ::LifeCycleEvent toProto(const ExtensionNotification&);
	static ::LifeCycleEvent toProto(const ClearContextRequest&);
	static ::LifeCycleEvent toProto(const ClearContextResponse&);
	static ::LifeCycleEvent toProto(const StatusRequest&);
	static ::LifeCycleEvent toProto(const StatusResponse&);
};

}

#endif /* end of include guard: MMIPROTOBRIDGE_H_T6VXUX69 */
