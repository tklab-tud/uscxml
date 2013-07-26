/* -*- Mode: C -*- */
/*======================================================================
  FILE: icalvalue.h
  CREATOR: eric 20 March 1999


  $Id: icalderivedvalue.h.in,v 1.10 2007-04-30 13:57:48 artcancro Exp $
  $Locker:  $

  

 (C) COPYRIGHT 2000, Eric Busboom, http://www.softwarestudio.org

 This program is free software; you can redistribute it and/or modify
 it under the terms of either: 

    The LGPL as published by the Free Software Foundation, version
    2.1, available at: http://www.fsf.org/copyleft/lesser.html

  Or:

    The Mozilla Public License Version 1.0. You may obtain a copy of
    the License at http://www.mozilla.org/MPL/

  The original code is icalvalue.h

  ======================================================================*/

#ifndef ICALDERIVEDVALUE_H
#define ICALDERIVEDVALUE_H

#include "icaltypes.h"
#include "icalrecur.h"
#include "icaltime.h"
#include "icalduration.h"
#include "icalperiod.h"
#include "icalattach.h"
     
typedef struct icalvalue_impl icalvalue;

void icalvalue_set_x(icalvalue* value, const char* v);
icalvalue* icalvalue_new_x(const char* v);
const char* icalvalue_get_x(const icalvalue* value);

icalvalue* icalvalue_new_recur (struct icalrecurrencetype v);
void icalvalue_set_recur(icalvalue* value, struct icalrecurrencetype v);
struct icalrecurrencetype icalvalue_get_recur(const icalvalue* value);

icalvalue* icalvalue_new_trigger (struct icaltriggertype v);
void icalvalue_set_trigger(icalvalue* value, struct icaltriggertype v);
struct icaltriggertype icalvalue_get_trigger(const icalvalue* value);

icalvalue* icalvalue_new_datetime(struct icaltimetype v);
struct icaltimetype icalvalue_get_datetime(const icalvalue* value);
void icalvalue_set_datetime(icalvalue* value, struct icaltimetype v);

icalvalue* icalvalue_new_datetimeperiod (struct icaldatetimeperiodtype v);
void icalvalue_set_datetimeperiod(icalvalue* value, struct icaldatetimeperiodtype v);
struct icaldatetimeperiodtype icalvalue_get_datetimeperiod(const icalvalue* value);

/* GEO */
icalvalue* icalvalue_new_geo(struct icalgeotype v);
struct icalgeotype icalvalue_get_geo(const icalvalue* value);
void icalvalue_set_geo(icalvalue* value, struct icalgeotype v);

icalvalue *icalvalue_new_attach (icalattach *attach);
void icalvalue_set_attach (icalvalue *value, icalattach *attach);
icalattach *icalvalue_get_attach (const icalvalue *value);

void icalvalue_reset_kind(icalvalue* value);

typedef enum icalvalue_kind {
   ICAL_ANY_VALUE=5000,
    ICAL_QUERY_VALUE=5001,
    ICAL_DATE_VALUE=5002,
    ICAL_ATTACH_VALUE=5003,
    ICAL_GEO_VALUE=5004,
    ICAL_STATUS_VALUE=5005,
    ICAL_TRANSP_VALUE=5006,
    ICAL_STRING_VALUE=5007,
    ICAL_TEXT_VALUE=5008,
    ICAL_REQUESTSTATUS_VALUE=5009,
    ICAL_CMD_VALUE=5010,
    ICAL_BINARY_VALUE=5011,
    ICAL_QUERYLEVEL_VALUE=5012,
    ICAL_PERIOD_VALUE=5013,
    ICAL_FLOAT_VALUE=5014,
    ICAL_DATETIMEPERIOD_VALUE=5015,
    ICAL_CARLEVEL_VALUE=5016,
    ICAL_INTEGER_VALUE=5017,
    ICAL_CLASS_VALUE=5018,
    ICAL_URI_VALUE=5019,
    ICAL_DURATION_VALUE=5020,
    ICAL_BOOLEAN_VALUE=5021,
    ICAL_X_VALUE=5022,
    ICAL_CALADDRESS_VALUE=5023,
    ICAL_TRIGGER_VALUE=5024,
    ICAL_XLICCLASS_VALUE=5025,
    ICAL_RECUR_VALUE=5026,
    ICAL_ACTION_VALUE=5027,
    ICAL_DATETIME_VALUE=5028,
    ICAL_UTCOFFSET_VALUE=5029,
    ICAL_METHOD_VALUE=5030,
   ICAL_NO_VALUE=5031
} icalvalue_kind ;

#define ICALPROPERTY_FIRST_ENUM 10000

typedef enum icalproperty_action {
    ICAL_ACTION_X = 10000,
    ICAL_ACTION_AUDIO = 10001,
    ICAL_ACTION_DISPLAY = 10002,
    ICAL_ACTION_EMAIL = 10003,
    ICAL_ACTION_PROCEDURE = 10004,
    ICAL_ACTION_NONE = 10005
} icalproperty_action;

typedef enum icalproperty_carlevel {
    ICAL_CARLEVEL_X = 10006,
    ICAL_CARLEVEL_CARNONE = 10007,
    ICAL_CARLEVEL_CARMIN = 10008,
    ICAL_CARLEVEL_CARFULL1 = 10009,
    ICAL_CARLEVEL_NONE = 10010
} icalproperty_carlevel;

typedef enum icalproperty_class {
    ICAL_CLASS_X = 10011,
    ICAL_CLASS_PUBLIC = 10012,
    ICAL_CLASS_PRIVATE = 10013,
    ICAL_CLASS_CONFIDENTIAL = 10014,
    ICAL_CLASS_NONE = 10015
} icalproperty_class;

typedef enum icalproperty_cmd {
    ICAL_CMD_X = 10016,
    ICAL_CMD_ABORT = 10017,
    ICAL_CMD_CONTINUE = 10018,
    ICAL_CMD_CREATE = 10019,
    ICAL_CMD_DELETE = 10020,
    ICAL_CMD_GENERATEUID = 10021,
    ICAL_CMD_GETCAPABILITY = 10022,
    ICAL_CMD_IDENTIFY = 10023,
    ICAL_CMD_MODIFY = 10024,
    ICAL_CMD_MOVE = 10025,
    ICAL_CMD_REPLY = 10026,
    ICAL_CMD_SEARCH = 10027,
    ICAL_CMD_SETLOCALE = 10028,
    ICAL_CMD_NONE = 10029
} icalproperty_cmd;

typedef enum icalproperty_method {
    ICAL_METHOD_X = 10030,
    ICAL_METHOD_PUBLISH = 10031,
    ICAL_METHOD_REQUEST = 10032,
    ICAL_METHOD_REPLY = 10033,
    ICAL_METHOD_ADD = 10034,
    ICAL_METHOD_CANCEL = 10035,
    ICAL_METHOD_REFRESH = 10036,
    ICAL_METHOD_COUNTER = 10037,
    ICAL_METHOD_DECLINECOUNTER = 10038,
    ICAL_METHOD_CREATE = 10039,
    ICAL_METHOD_READ = 10040,
    ICAL_METHOD_RESPONSE = 10041,
    ICAL_METHOD_MOVE = 10042,
    ICAL_METHOD_MODIFY = 10043,
    ICAL_METHOD_GENERATEUID = 10044,
    ICAL_METHOD_DELETE = 10045,
    ICAL_METHOD_NONE = 10046
} icalproperty_method;

typedef enum icalproperty_querylevel {
    ICAL_QUERYLEVEL_X = 10047,
    ICAL_QUERYLEVEL_CALQL1 = 10048,
    ICAL_QUERYLEVEL_CALQLNONE = 10049,
    ICAL_QUERYLEVEL_NONE = 10050
} icalproperty_querylevel;

typedef enum icalproperty_status {
    ICAL_STATUS_X = 10051,
    ICAL_STATUS_TENTATIVE = 10052,
    ICAL_STATUS_CONFIRMED = 10053,
    ICAL_STATUS_COMPLETED = 10054,
    ICAL_STATUS_NEEDSACTION = 10055,
    ICAL_STATUS_CANCELLED = 10056,
    ICAL_STATUS_INPROCESS = 10057,
    ICAL_STATUS_DRAFT = 10058,
    ICAL_STATUS_FINAL = 10059,
    ICAL_STATUS_NONE = 10060
} icalproperty_status;

typedef enum icalproperty_transp {
    ICAL_TRANSP_X = 10061,
    ICAL_TRANSP_OPAQUE = 10062,
    ICAL_TRANSP_OPAQUENOCONFLICT = 10063,
    ICAL_TRANSP_TRANSPARENT = 10064,
    ICAL_TRANSP_TRANSPARENTNOCONFLICT = 10065,
    ICAL_TRANSP_NONE = 10066
} icalproperty_transp;

typedef enum icalproperty_xlicclass {
    ICAL_XLICCLASS_X = 10067,
    ICAL_XLICCLASS_PUBLISHNEW = 10068,
    ICAL_XLICCLASS_PUBLISHUPDATE = 10069,
    ICAL_XLICCLASS_PUBLISHFREEBUSY = 10070,
    ICAL_XLICCLASS_REQUESTNEW = 10071,
    ICAL_XLICCLASS_REQUESTUPDATE = 10072,
    ICAL_XLICCLASS_REQUESTRESCHEDULE = 10073,
    ICAL_XLICCLASS_REQUESTDELEGATE = 10074,
    ICAL_XLICCLASS_REQUESTNEWORGANIZER = 10075,
    ICAL_XLICCLASS_REQUESTFORWARD = 10076,
    ICAL_XLICCLASS_REQUESTSTATUS = 10077,
    ICAL_XLICCLASS_REQUESTFREEBUSY = 10078,
    ICAL_XLICCLASS_REPLYACCEPT = 10079,
    ICAL_XLICCLASS_REPLYDECLINE = 10080,
    ICAL_XLICCLASS_REPLYDELEGATE = 10081,
    ICAL_XLICCLASS_REPLYCRASHERACCEPT = 10082,
    ICAL_XLICCLASS_REPLYCRASHERDECLINE = 10083,
    ICAL_XLICCLASS_ADDINSTANCE = 10084,
    ICAL_XLICCLASS_CANCELEVENT = 10085,
    ICAL_XLICCLASS_CANCELINSTANCE = 10086,
    ICAL_XLICCLASS_CANCELALL = 10087,
    ICAL_XLICCLASS_REFRESH = 10088,
    ICAL_XLICCLASS_COUNTER = 10089,
    ICAL_XLICCLASS_DECLINECOUNTER = 10090,
    ICAL_XLICCLASS_MALFORMED = 10091,
    ICAL_XLICCLASS_OBSOLETE = 10092,
    ICAL_XLICCLASS_MISSEQUENCED = 10093,
    ICAL_XLICCLASS_UNKNOWN = 10094,
    ICAL_XLICCLASS_NONE = 10095
} icalproperty_xlicclass;

#define ICALPROPERTY_LAST_ENUM 10096


 /* QUERY */ 
icalvalue* icalvalue_new_query(const char* v); 
const char* icalvalue_get_query(const icalvalue* value); 
void icalvalue_set_query(icalvalue* value, const char* v);


 /* DATE */ 
icalvalue* icalvalue_new_date(struct icaltimetype v); 
struct icaltimetype icalvalue_get_date(const icalvalue* value); 
void icalvalue_set_date(icalvalue* value, struct icaltimetype v);


 /* STATUS */ 
icalvalue* icalvalue_new_status(enum icalproperty_status v); 
enum icalproperty_status icalvalue_get_status(const icalvalue* value); 
void icalvalue_set_status(icalvalue* value, enum icalproperty_status v);


 /* TRANSP */ 
icalvalue* icalvalue_new_transp(enum icalproperty_transp v); 
enum icalproperty_transp icalvalue_get_transp(const icalvalue* value); 
void icalvalue_set_transp(icalvalue* value, enum icalproperty_transp v);


 /* STRING */ 
icalvalue* icalvalue_new_string(const char* v); 
const char* icalvalue_get_string(const icalvalue* value); 
void icalvalue_set_string(icalvalue* value, const char* v);


 /* TEXT */ 
icalvalue* icalvalue_new_text(const char* v); 
const char* icalvalue_get_text(const icalvalue* value); 
void icalvalue_set_text(icalvalue* value, const char* v);


 /* REQUEST-STATUS */ 
icalvalue* icalvalue_new_requeststatus(struct icalreqstattype v); 
struct icalreqstattype icalvalue_get_requeststatus(const icalvalue* value); 
void icalvalue_set_requeststatus(icalvalue* value, struct icalreqstattype v);


 /* CMD */ 
icalvalue* icalvalue_new_cmd(enum icalproperty_cmd v); 
enum icalproperty_cmd icalvalue_get_cmd(const icalvalue* value); 
void icalvalue_set_cmd(icalvalue* value, enum icalproperty_cmd v);


 /* BINARY */ 
icalvalue* icalvalue_new_binary(const char* v); 
const char* icalvalue_get_binary(const icalvalue* value); 
void icalvalue_set_binary(icalvalue* value, const char* v);


 /* QUERY-LEVEL */ 
icalvalue* icalvalue_new_querylevel(enum icalproperty_querylevel v); 
enum icalproperty_querylevel icalvalue_get_querylevel(const icalvalue* value); 
void icalvalue_set_querylevel(icalvalue* value, enum icalproperty_querylevel v);


 /* PERIOD */ 
icalvalue* icalvalue_new_period(struct icalperiodtype v); 
struct icalperiodtype icalvalue_get_period(const icalvalue* value); 
void icalvalue_set_period(icalvalue* value, struct icalperiodtype v);


 /* FLOAT */ 
icalvalue* icalvalue_new_float(float v); 
float icalvalue_get_float(const icalvalue* value); 
void icalvalue_set_float(icalvalue* value, float v);


 /* CAR-LEVEL */ 
icalvalue* icalvalue_new_carlevel(enum icalproperty_carlevel v); 
enum icalproperty_carlevel icalvalue_get_carlevel(const icalvalue* value); 
void icalvalue_set_carlevel(icalvalue* value, enum icalproperty_carlevel v);


 /* INTEGER */ 
icalvalue* icalvalue_new_integer(int v); 
int icalvalue_get_integer(const icalvalue* value); 
void icalvalue_set_integer(icalvalue* value, int v);


 /* URI */ 
icalvalue* icalvalue_new_uri(const char* v); 
const char* icalvalue_get_uri(const icalvalue* value); 
void icalvalue_set_uri(icalvalue* value, const char* v);


 /* DURATION */ 
icalvalue* icalvalue_new_duration(struct icaldurationtype v); 
struct icaldurationtype icalvalue_get_duration(const icalvalue* value); 
void icalvalue_set_duration(icalvalue* value, struct icaldurationtype v);


 /* BOOLEAN */ 
icalvalue* icalvalue_new_boolean(int v); 
int icalvalue_get_boolean(const icalvalue* value); 
void icalvalue_set_boolean(icalvalue* value, int v);


 /* CAL-ADDRESS */ 
icalvalue* icalvalue_new_caladdress(const char* v); 
const char* icalvalue_get_caladdress(const icalvalue* value); 
void icalvalue_set_caladdress(icalvalue* value, const char* v);


 /* X-LIC-CLASS */ 
icalvalue* icalvalue_new_xlicclass(enum icalproperty_xlicclass v); 
enum icalproperty_xlicclass icalvalue_get_xlicclass(const icalvalue* value); 
void icalvalue_set_xlicclass(icalvalue* value, enum icalproperty_xlicclass v);


 /* ACTION */ 
icalvalue* icalvalue_new_action(enum icalproperty_action v); 
enum icalproperty_action icalvalue_get_action(const icalvalue* value); 
void icalvalue_set_action(icalvalue* value, enum icalproperty_action v);


 /* UTC-OFFSET */ 
icalvalue* icalvalue_new_utcoffset(int v); 
int icalvalue_get_utcoffset(const icalvalue* value); 
void icalvalue_set_utcoffset(icalvalue* value, int v);


 /* METHOD */ 
icalvalue* icalvalue_new_method(enum icalproperty_method v); 
enum icalproperty_method icalvalue_get_method(const icalvalue* value); 
void icalvalue_set_method(icalvalue* value, enum icalproperty_method v);

#endif /*ICALVALUE_H*/


icalvalue* icalvalue_new_class(enum icalproperty_class v);
enum icalproperty_class icalvalue_get_class(const icalvalue* value);
void icalvalue_set_class(icalvalue* value, enum icalproperty_class v);
