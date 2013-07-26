/* -*- Mode: C -*- */
/*======================================================================
  FILE: icalparam.h
  CREATOR: eric 20 March 1999


  $Id: icalderivedparameter.h.in,v 1.4 2007-04-30 13:57:48 artcancro Exp $
  $Locker:  $

  

 (C) COPYRIGHT 2000, Eric Busboom, http://www.softwarestudio.org

 This program is free software; you can redistribute it and/or modify
 it under the terms of either: 

    The LGPL as published by the Free Software Foundation, version
    2.1, available at: http://www.fsf.org/copyleft/lesser.html

  Or:

    The Mozilla Public License Version 1.0. You may obtain a copy of
    the License at http://www.mozilla.org/MPL/

  The original code is icalparam.h

  ======================================================================*/

#ifndef ICALDERIVEDPARAMETER_H
#define ICALDERIVEDPARAMETER_H


typedef struct icalparameter_impl icalparameter;

const char* icalparameter_enum_to_string(int e);
int icalparameter_string_to_enum(const char* str); 

/* START of section of machine generated code (mkderivedparameters.pl). Do not edit. */

typedef enum icalparameter_kind {
    ICAL_ANY_PARAMETER = 0,
    ICAL_ACTIONPARAM_PARAMETER = 1, 
    ICAL_ALTREP_PARAMETER = 2, 
    ICAL_CHARSET_PARAMETER = 3, 
    ICAL_CN_PARAMETER = 4, 
    ICAL_CUTYPE_PARAMETER = 5, 
    ICAL_DELEGATEDFROM_PARAMETER = 6, 
    ICAL_DELEGATEDTO_PARAMETER = 7, 
    ICAL_DIR_PARAMETER = 8, 
    ICAL_ENABLE_PARAMETER = 9, 
    ICAL_ENCODING_PARAMETER = 10, 
    ICAL_FBTYPE_PARAMETER = 11, 
    ICAL_FMTTYPE_PARAMETER = 12, 
    ICAL_IANA_PARAMETER = 33, 
    ICAL_ID_PARAMETER = 13, 
    ICAL_LANGUAGE_PARAMETER = 14, 
    ICAL_LATENCY_PARAMETER = 15, 
    ICAL_LOCAL_PARAMETER = 16, 
    ICAL_LOCALIZE_PARAMETER = 17, 
    ICAL_MEMBER_PARAMETER = 18, 
    ICAL_OPTIONS_PARAMETER = 19, 
    ICAL_PARTSTAT_PARAMETER = 20, 
    ICAL_RANGE_PARAMETER = 21, 
    ICAL_RELATED_PARAMETER = 22, 
    ICAL_RELTYPE_PARAMETER = 23, 
    ICAL_ROLE_PARAMETER = 24, 
    ICAL_RSVP_PARAMETER = 25, 
    ICAL_SCHEDULEAGENT_PARAMETER = 34, 
    ICAL_SCHEDULEFORCESEND_PARAMETER = 35, 
    ICAL_SCHEDULESTATUS_PARAMETER = 36, 
    ICAL_SENTBY_PARAMETER = 26, 
    ICAL_TZID_PARAMETER = 27, 
    ICAL_VALUE_PARAMETER = 28, 
    ICAL_X_PARAMETER = 29, 
    ICAL_XLICCOMPARETYPE_PARAMETER = 30, 
    ICAL_XLICERRORTYPE_PARAMETER = 31, 
    ICAL_NO_PARAMETER = 32
} icalparameter_kind;

#define ICALPARAMETER_FIRST_ENUM 20000

typedef enum icalparameter_action {
    ICAL_ACTIONPARAM_X = 20000,
    ICAL_ACTIONPARAM_ASK = 20001,
    ICAL_ACTIONPARAM_ABORT = 20002,
    ICAL_ACTIONPARAM_NONE = 20003
} icalparameter_action;

typedef enum icalparameter_cutype {
    ICAL_CUTYPE_X = 20004,
    ICAL_CUTYPE_INDIVIDUAL = 20005,
    ICAL_CUTYPE_GROUP = 20006,
    ICAL_CUTYPE_RESOURCE = 20007,
    ICAL_CUTYPE_ROOM = 20008,
    ICAL_CUTYPE_UNKNOWN = 20009,
    ICAL_CUTYPE_NONE = 20010
} icalparameter_cutype;

typedef enum icalparameter_enable {
    ICAL_ENABLE_X = 20011,
    ICAL_ENABLE_TRUE = 20012,
    ICAL_ENABLE_FALSE = 20013,
    ICAL_ENABLE_NONE = 20014
} icalparameter_enable;

typedef enum icalparameter_encoding {
    ICAL_ENCODING_X = 20015,
    ICAL_ENCODING_8BIT = 20016,
    ICAL_ENCODING_BASE64 = 20017,
    ICAL_ENCODING_NONE = 20018
} icalparameter_encoding;

typedef enum icalparameter_fbtype {
    ICAL_FBTYPE_X = 20019,
    ICAL_FBTYPE_FREE = 20020,
    ICAL_FBTYPE_BUSY = 20021,
    ICAL_FBTYPE_BUSYUNAVAILABLE = 20022,
    ICAL_FBTYPE_BUSYTENTATIVE = 20023,
    ICAL_FBTYPE_NONE = 20024
} icalparameter_fbtype;

typedef enum icalparameter_local {
    ICAL_LOCAL_X = 20025,
    ICAL_LOCAL_TRUE = 20026,
    ICAL_LOCAL_FALSE = 20027,
    ICAL_LOCAL_NONE = 20028
} icalparameter_local;

typedef enum icalparameter_partstat {
    ICAL_PARTSTAT_X = 20029,
    ICAL_PARTSTAT_NEEDSACTION = 20030,
    ICAL_PARTSTAT_ACCEPTED = 20031,
    ICAL_PARTSTAT_DECLINED = 20032,
    ICAL_PARTSTAT_TENTATIVE = 20033,
    ICAL_PARTSTAT_DELEGATED = 20034,
    ICAL_PARTSTAT_COMPLETED = 20035,
    ICAL_PARTSTAT_INPROCESS = 20036,
    ICAL_PARTSTAT_NONE = 20037
} icalparameter_partstat;

typedef enum icalparameter_range {
    ICAL_RANGE_X = 20038,
    ICAL_RANGE_THISANDPRIOR = 20039,
    ICAL_RANGE_THISANDFUTURE = 20040,
    ICAL_RANGE_NONE = 20041
} icalparameter_range;

typedef enum icalparameter_related {
    ICAL_RELATED_X = 20042,
    ICAL_RELATED_START = 20043,
    ICAL_RELATED_END = 20044,
    ICAL_RELATED_NONE = 20045
} icalparameter_related;

typedef enum icalparameter_reltype {
    ICAL_RELTYPE_X = 20046,
    ICAL_RELTYPE_PARENT = 20047,
    ICAL_RELTYPE_CHILD = 20048,
    ICAL_RELTYPE_SIBLING = 20049,
    ICAL_RELTYPE_NONE = 20050
} icalparameter_reltype;

typedef enum icalparameter_role {
    ICAL_ROLE_X = 20051,
    ICAL_ROLE_CHAIR = 20052,
    ICAL_ROLE_REQPARTICIPANT = 20053,
    ICAL_ROLE_OPTPARTICIPANT = 20054,
    ICAL_ROLE_NONPARTICIPANT = 20055,
    ICAL_ROLE_NONE = 20056
} icalparameter_role;

typedef enum icalparameter_rsvp {
    ICAL_RSVP_X = 20057,
    ICAL_RSVP_TRUE = 20058,
    ICAL_RSVP_FALSE = 20059,
    ICAL_RSVP_NONE = 20060
} icalparameter_rsvp;

typedef enum icalparameter_scheduleagent {
    ICAL_SCHEDULEAGENT_X = 20061,
    ICAL_SCHEDULEAGENT_SERVER = 20062,
    ICAL_SCHEDULEAGENT_CLIENT = 20063,
    ICAL_SCHEDULEAGENT_NONE = 20064
} icalparameter_scheduleagent;

typedef enum icalparameter_scheduleforcesend {
    ICAL_SCHEDULEFORCESEND_X = 20065,
    ICAL_SCHEDULEFORCESEND_REQUEST = 20066,
    ICAL_SCHEDULEFORCESEND_REPLY = 20067,
    ICAL_SCHEDULEFORCESEND_NONE = 20068
} icalparameter_scheduleforcesend;

typedef enum icalparameter_value {
    ICAL_VALUE_X = 20069,
    ICAL_VALUE_BINARY = 20070,
    ICAL_VALUE_BOOLEAN = 20071,
    ICAL_VALUE_DATE = 20072,
    ICAL_VALUE_DURATION = 20073,
    ICAL_VALUE_FLOAT = 20074,
    ICAL_VALUE_INTEGER = 20075,
    ICAL_VALUE_PERIOD = 20076,
    ICAL_VALUE_RECUR = 20077,
    ICAL_VALUE_TEXT = 20078,
    ICAL_VALUE_URI = 20079,
    ICAL_VALUE_ERROR = 20080,
    ICAL_VALUE_DATETIME = 20081,
    ICAL_VALUE_UTCOFFSET = 20082,
    ICAL_VALUE_CALADDRESS = 20083,
    ICAL_VALUE_NONE = 20084
} icalparameter_value;

typedef enum icalparameter_xliccomparetype {
    ICAL_XLICCOMPARETYPE_X = 20085,
    ICAL_XLICCOMPARETYPE_EQUAL = 20086,
    ICAL_XLICCOMPARETYPE_NOTEQUAL = 20087,
    ICAL_XLICCOMPARETYPE_LESS = 20088,
    ICAL_XLICCOMPARETYPE_GREATER = 20089,
    ICAL_XLICCOMPARETYPE_LESSEQUAL = 20090,
    ICAL_XLICCOMPARETYPE_GREATEREQUAL = 20091,
    ICAL_XLICCOMPARETYPE_REGEX = 20092,
    ICAL_XLICCOMPARETYPE_ISNULL = 20093,
    ICAL_XLICCOMPARETYPE_ISNOTNULL = 20094,
    ICAL_XLICCOMPARETYPE_NONE = 20095
} icalparameter_xliccomparetype;

typedef enum icalparameter_xlicerrortype {
    ICAL_XLICERRORTYPE_X = 20096,
    ICAL_XLICERRORTYPE_COMPONENTPARSEERROR = 20097,
    ICAL_XLICERRORTYPE_PROPERTYPARSEERROR = 20098,
    ICAL_XLICERRORTYPE_PARAMETERNAMEPARSEERROR = 20099,
    ICAL_XLICERRORTYPE_PARAMETERVALUEPARSEERROR = 20100,
    ICAL_XLICERRORTYPE_VALUEPARSEERROR = 20101,
    ICAL_XLICERRORTYPE_INVALIDITIP = 20102,
    ICAL_XLICERRORTYPE_UNKNOWNVCALPROPERROR = 20103,
    ICAL_XLICERRORTYPE_MIMEPARSEERROR = 20104,
    ICAL_XLICERRORTYPE_VCALPROPPARSEERROR = 20105,
    ICAL_XLICERRORTYPE_NONE = 20106
} icalparameter_xlicerrortype;

#define ICALPARAMETER_LAST_ENUM 20107

/* ACTIONPARAM */
icalparameter* icalparameter_new_actionparam(icalparameter_action v);
icalparameter_action icalparameter_get_actionparam(const icalparameter* value);
void icalparameter_set_actionparam(icalparameter* value, icalparameter_action v);

/* ALTREP */
icalparameter* icalparameter_new_altrep(const char* v);
const char* icalparameter_get_altrep(const icalparameter* value);
void icalparameter_set_altrep(icalparameter* value, const char* v);

/* CHARSET */
icalparameter* icalparameter_new_charset(const char* v);
const char* icalparameter_get_charset(const icalparameter* value);
void icalparameter_set_charset(icalparameter* value, const char* v);

/* CN */
icalparameter* icalparameter_new_cn(const char* v);
const char* icalparameter_get_cn(const icalparameter* value);
void icalparameter_set_cn(icalparameter* value, const char* v);

/* CUTYPE */
icalparameter* icalparameter_new_cutype(icalparameter_cutype v);
icalparameter_cutype icalparameter_get_cutype(const icalparameter* value);
void icalparameter_set_cutype(icalparameter* value, icalparameter_cutype v);

/* DELEGATED-FROM */
icalparameter* icalparameter_new_delegatedfrom(const char* v);
const char* icalparameter_get_delegatedfrom(const icalparameter* value);
void icalparameter_set_delegatedfrom(icalparameter* value, const char* v);

/* DELEGATED-TO */
icalparameter* icalparameter_new_delegatedto(const char* v);
const char* icalparameter_get_delegatedto(const icalparameter* value);
void icalparameter_set_delegatedto(icalparameter* value, const char* v);

/* DIR */
icalparameter* icalparameter_new_dir(const char* v);
const char* icalparameter_get_dir(const icalparameter* value);
void icalparameter_set_dir(icalparameter* value, const char* v);

/* ENABLE */
icalparameter* icalparameter_new_enable(icalparameter_enable v);
icalparameter_enable icalparameter_get_enable(const icalparameter* value);
void icalparameter_set_enable(icalparameter* value, icalparameter_enable v);

/* ENCODING */
icalparameter* icalparameter_new_encoding(icalparameter_encoding v);
icalparameter_encoding icalparameter_get_encoding(const icalparameter* value);
void icalparameter_set_encoding(icalparameter* value, icalparameter_encoding v);

/* FBTYPE */
icalparameter* icalparameter_new_fbtype(icalparameter_fbtype v);
icalparameter_fbtype icalparameter_get_fbtype(const icalparameter* value);
void icalparameter_set_fbtype(icalparameter* value, icalparameter_fbtype v);

/* FMTTYPE */
icalparameter* icalparameter_new_fmttype(const char* v);
const char* icalparameter_get_fmttype(const icalparameter* value);
void icalparameter_set_fmttype(icalparameter* value, const char* v);

/* IANA */
icalparameter* icalparameter_new_iana(const char* v);
const char* icalparameter_get_iana(const icalparameter* value);
void icalparameter_set_iana(icalparameter* value, const char* v);

/* ID */
icalparameter* icalparameter_new_id(const char* v);
const char* icalparameter_get_id(const icalparameter* value);
void icalparameter_set_id(icalparameter* value, const char* v);

/* LANGUAGE */
icalparameter* icalparameter_new_language(const char* v);
const char* icalparameter_get_language(const icalparameter* value);
void icalparameter_set_language(icalparameter* value, const char* v);

/* LATENCY */
icalparameter* icalparameter_new_latency(const char* v);
const char* icalparameter_get_latency(const icalparameter* value);
void icalparameter_set_latency(icalparameter* value, const char* v);

/* LOCAL */
icalparameter* icalparameter_new_local(icalparameter_local v);
icalparameter_local icalparameter_get_local(const icalparameter* value);
void icalparameter_set_local(icalparameter* value, icalparameter_local v);

/* LOCALIZE */
icalparameter* icalparameter_new_localize(const char* v);
const char* icalparameter_get_localize(const icalparameter* value);
void icalparameter_set_localize(icalparameter* value, const char* v);

/* MEMBER */
icalparameter* icalparameter_new_member(const char* v);
const char* icalparameter_get_member(const icalparameter* value);
void icalparameter_set_member(icalparameter* value, const char* v);

/* OPTIONS */
icalparameter* icalparameter_new_options(const char* v);
const char* icalparameter_get_options(const icalparameter* value);
void icalparameter_set_options(icalparameter* value, const char* v);

/* PARTSTAT */
icalparameter* icalparameter_new_partstat(icalparameter_partstat v);
icalparameter_partstat icalparameter_get_partstat(const icalparameter* value);
void icalparameter_set_partstat(icalparameter* value, icalparameter_partstat v);

/* RANGE */
icalparameter* icalparameter_new_range(icalparameter_range v);
icalparameter_range icalparameter_get_range(const icalparameter* value);
void icalparameter_set_range(icalparameter* value, icalparameter_range v);

/* RELATED */
icalparameter* icalparameter_new_related(icalparameter_related v);
icalparameter_related icalparameter_get_related(const icalparameter* value);
void icalparameter_set_related(icalparameter* value, icalparameter_related v);

/* RELTYPE */
icalparameter* icalparameter_new_reltype(icalparameter_reltype v);
icalparameter_reltype icalparameter_get_reltype(const icalparameter* value);
void icalparameter_set_reltype(icalparameter* value, icalparameter_reltype v);

/* ROLE */
icalparameter* icalparameter_new_role(icalparameter_role v);
icalparameter_role icalparameter_get_role(const icalparameter* value);
void icalparameter_set_role(icalparameter* value, icalparameter_role v);

/* RSVP */
icalparameter* icalparameter_new_rsvp(icalparameter_rsvp v);
icalparameter_rsvp icalparameter_get_rsvp(const icalparameter* value);
void icalparameter_set_rsvp(icalparameter* value, icalparameter_rsvp v);

/* SCHEDULE-AGENT */
icalparameter* icalparameter_new_scheduleagent(icalparameter_scheduleagent v);
icalparameter_scheduleagent icalparameter_get_scheduleagent(const icalparameter* value);
void icalparameter_set_scheduleagent(icalparameter* value, icalparameter_scheduleagent v);

/* SCHEDULE-FORCE-SEND */
icalparameter* icalparameter_new_scheduleforcesend(icalparameter_scheduleforcesend v);
icalparameter_scheduleforcesend icalparameter_get_scheduleforcesend(const icalparameter* value);
void icalparameter_set_scheduleforcesend(icalparameter* value, icalparameter_scheduleforcesend v);

/* SCHEDULE-STATUS */
icalparameter* icalparameter_new_schedulestatus(const char* v);
const char* icalparameter_get_schedulestatus(const icalparameter* value);
void icalparameter_set_schedulestatus(icalparameter* value, const char* v);

/* SENT-BY */
icalparameter* icalparameter_new_sentby(const char* v);
const char* icalparameter_get_sentby(const icalparameter* value);
void icalparameter_set_sentby(icalparameter* value, const char* v);

/* TZID */
icalparameter* icalparameter_new_tzid(const char* v);
const char* icalparameter_get_tzid(const icalparameter* value);
void icalparameter_set_tzid(icalparameter* value, const char* v);

/* VALUE */
icalparameter* icalparameter_new_value(icalparameter_value v);
icalparameter_value icalparameter_get_value(const icalparameter* value);
void icalparameter_set_value(icalparameter* value, icalparameter_value v);

/* X */
icalparameter* icalparameter_new_x(const char* v);
const char* icalparameter_get_x(const icalparameter* value);
void icalparameter_set_x(icalparameter* value, const char* v);

/* X-LIC-COMPARETYPE */
icalparameter* icalparameter_new_xliccomparetype(icalparameter_xliccomparetype v);
icalparameter_xliccomparetype icalparameter_get_xliccomparetype(const icalparameter* value);
void icalparameter_set_xliccomparetype(icalparameter* value, icalparameter_xliccomparetype v);

/* X-LIC-ERRORTYPE */
icalparameter* icalparameter_new_xlicerrortype(icalparameter_xlicerrortype v);
icalparameter_xlicerrortype icalparameter_get_xlicerrortype(const icalparameter* value);
void icalparameter_set_xlicerrortype(icalparameter* value, icalparameter_xlicerrortype v);

#endif /*ICALPARAMETER_H*/

/* END   of section of machine generated code (mkderivedparameters.pl). Do not edit. */

