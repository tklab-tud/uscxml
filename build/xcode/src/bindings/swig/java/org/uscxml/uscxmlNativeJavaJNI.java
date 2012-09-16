/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (http://www.swig.org).
 * Version 2.0.5
 *
 * Do not make changes to this file unless you know what you are doing--modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.uscxml;

public class uscxmlNativeJavaJNI {
  public final static native long new_Data__SWIG_0();
  public final static native long new_Data__SWIG_1(long jarg1, int jarg2);
  public final static native long new_Data__SWIG_2(long jarg1);
  public final static native void delete_Data(long jarg1);
  public final static native long Data_fromXML(long jarg1);
  public final static native long Data_toDocument(long jarg1, Data jarg1_);
  public final static native long Data_toXMLString(long jarg1, Data jarg1_);
  public final static native void Data_compound_set(long jarg1, Data jarg1_, long jarg2);
  public final static native long Data_compound_get(long jarg1, Data jarg1_);
  public final static native void Data_array_set(long jarg1, Data jarg1_, long jarg2);
  public final static native long Data_array_get(long jarg1, Data jarg1_);
  public final static native void Data_atom_set(long jarg1, Data jarg1_, long jarg2);
  public final static native long Data_atom_get(long jarg1, Data jarg1_);
  public final static native void Data_type_set(long jarg1, Data jarg1_, int jarg2);
  public final static native int Data_type_get(long jarg1, Data jarg1_);
  public final static native long new_Event();
  public final static native void Event_name_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_name_get(long jarg1, Event jarg1_);
  public final static native void Event_type_set(long jarg1, Event jarg1_, int jarg2);
  public final static native int Event_type_get(long jarg1, Event jarg1_);
  public final static native void Event_origin_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_origin_get(long jarg1, Event jarg1_);
  public final static native void Event_origintype_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_origintype_get(long jarg1, Event jarg1_);
  public final static native void Event_dom_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_dom_get(long jarg1, Event jarg1_);
  public final static native void Event_sendid_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_sendid_get(long jarg1, Event jarg1_);
  public final static native void Event_invokeid_set(long jarg1, Event jarg1_, long jarg2);
  public final static native long Event_invokeid_get(long jarg1, Event jarg1_);
  public final static native long Event_fromXML(long jarg1);
  public final static native long Event_toDocument(long jarg1, Event jarg1_);
  public final static native long Event_toXMLString(long jarg1, Event jarg1_);
  public final static native void delete_Event(long jarg1);
  public final static native void InvokeRequest_type_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_type_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_src_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_src_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_namelist_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_namelist_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_autoForward_set(long jarg1, InvokeRequest jarg1_, boolean jarg2);
  public final static native boolean InvokeRequest_autoForward_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_finalize_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_finalize_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_params_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_params_get(long jarg1, InvokeRequest jarg1_);
  public final static native void InvokeRequest_content_set(long jarg1, InvokeRequest jarg1_, long jarg2);
  public final static native long InvokeRequest_content_get(long jarg1, InvokeRequest jarg1_);
  public final static native long InvokeRequest_fromXML(long jarg1);
  public final static native long InvokeRequest_toDocument(long jarg1, InvokeRequest jarg1_);
  public final static native long InvokeRequest_toXMLString(long jarg1, InvokeRequest jarg1_);
  public final static native long new_InvokeRequest();
  public final static native void delete_InvokeRequest(long jarg1);
  public final static native void SendRequest_target_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_target_get(long jarg1, SendRequest jarg1_);
  public final static native void SendRequest_type_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_type_get(long jarg1, SendRequest jarg1_);
  public final static native void SendRequest_delayMs_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_delayMs_get(long jarg1, SendRequest jarg1_);
  public final static native void SendRequest_params_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_params_get(long jarg1, SendRequest jarg1_);
  public final static native void SendRequest_namelist_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_namelist_get(long jarg1, SendRequest jarg1_);
  public final static native void SendRequest_content_set(long jarg1, SendRequest jarg1_, long jarg2);
  public final static native long SendRequest_content_get(long jarg1, SendRequest jarg1_);
  public final static native long SendRequest_fromXML(long jarg1);
  public final static native long SendRequest_toDocument(long jarg1, SendRequest jarg1_);
  public final static native long SendRequest_toXMLString(long jarg1, SendRequest jarg1_);
  public final static native long new_SendRequest();
  public final static native void delete_SendRequest(long jarg1);
  public final static native long new_Interpreter(long jarg1);
  public final static native void delete_Interpreter(long jarg1);
  public final static native void Interpreter_start(long jarg1, Interpreter jarg1_);
  public final static native void Interpreter_stop(long jarg1, Interpreter jarg1_);
  public final static native void Interpreter_run(long jarg1);
  public final static native void Interpreter_interpret(long jarg1, Interpreter jarg1_);
  public final static native boolean Interpreter_validate(long jarg1, Interpreter jarg1_);
  public final static native void Interpreter_waitForStabilization(long jarg1, Interpreter jarg1_);
  public final static native void Interpreter_receive(long jarg1, Interpreter jarg1_, long jarg2, Event jarg2_);
  public final static native void Interpreter_receiveInternal(long jarg1, Interpreter jarg1_, long jarg2, Event jarg2_);
  public final static native long Interpreter_getConfiguration(long jarg1, Interpreter jarg1_);
  public final static native long Interpreter_getState(long jarg1, Interpreter jarg1_, long jarg2);
  public final static native long Interpreter_getName(long jarg1, Interpreter jarg1_);
  public final static native long Interpreter_getSessionId(long jarg1, Interpreter jarg1_);
  public final static native boolean Interpreter_isMember(long jarg1, long jarg2);
  public final static native void Interpreter_dump__SWIG_0(long jarg1, Interpreter jarg1_);
  public final static native void Interpreter_dump__SWIG_1(long jarg1, int jarg2);
  public final static native void Interpreter_dump__SWIG_2(long jarg1);
  public final static native long Event_SWIGUpcast(long jarg1);
  public final static native long InvokeRequest_SWIGUpcast(long jarg1);
  public final static native long SendRequest_SWIGUpcast(long jarg1);
}
