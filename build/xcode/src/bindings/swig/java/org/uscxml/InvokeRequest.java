/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (http://www.swig.org).
 * Version 2.0.5
 *
 * Do not make changes to this file unless you know what you are doing--modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */

package org.uscxml;

public class InvokeRequest extends Event {
  private long swigCPtr;

  protected InvokeRequest(long cPtr, boolean cMemoryOwn) {
    super(uscxmlNativeJavaJNI.InvokeRequest_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
  }

  protected static long getCPtr(InvokeRequest obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected void finalize() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        uscxmlNativeJavaJNI.delete_InvokeRequest(swigCPtr);
      }
      swigCPtr = 0;
    }
    super.delete();
  }

  public void setType(SWIGTYPE_p_std__string value) {
    uscxmlNativeJavaJNI.InvokeRequest_type_set(swigCPtr, this, SWIGTYPE_p_std__string.getCPtr(value));
  }

  public SWIGTYPE_p_std__string getType() {
    return new SWIGTYPE_p_std__string(uscxmlNativeJavaJNI.InvokeRequest_type_get(swigCPtr, this), true);
  }

  public void setSrc(SWIGTYPE_p_std__string value) {
    uscxmlNativeJavaJNI.InvokeRequest_src_set(swigCPtr, this, SWIGTYPE_p_std__string.getCPtr(value));
  }

  public SWIGTYPE_p_std__string getSrc() {
    return new SWIGTYPE_p_std__string(uscxmlNativeJavaJNI.InvokeRequest_src_get(swigCPtr, this), true);
  }

  public void setNamelist(SWIGTYPE_p_std__string value) {
    uscxmlNativeJavaJNI.InvokeRequest_namelist_set(swigCPtr, this, SWIGTYPE_p_std__string.getCPtr(value));
  }

  public SWIGTYPE_p_std__string getNamelist() {
    return new SWIGTYPE_p_std__string(uscxmlNativeJavaJNI.InvokeRequest_namelist_get(swigCPtr, this), true);
  }

  public void setAutoForward(boolean value) {
    uscxmlNativeJavaJNI.InvokeRequest_autoForward_set(swigCPtr, this, value);
  }

  public boolean getAutoForward() {
    return uscxmlNativeJavaJNI.InvokeRequest_autoForward_get(swigCPtr, this);
  }

  public void setFinalize(SWIGTYPE_p_Arabica__DOM__NodeT_std__string_t value) {
    uscxmlNativeJavaJNI.InvokeRequest_finalize_set(swigCPtr, this, SWIGTYPE_p_Arabica__DOM__NodeT_std__string_t.getCPtr(value));
  }

  public SWIGTYPE_p_Arabica__DOM__NodeT_std__string_t getFinalize() {
    return new SWIGTYPE_p_Arabica__DOM__NodeT_std__string_t(uscxmlNativeJavaJNI.InvokeRequest_finalize_get(swigCPtr, this), true);
  }

  public void setParams(SWIGTYPE_p_std__mapT_std__string_std__string_t value) {
    uscxmlNativeJavaJNI.InvokeRequest_params_set(swigCPtr, this, SWIGTYPE_p_std__mapT_std__string_std__string_t.getCPtr(value));
  }

  public SWIGTYPE_p_std__mapT_std__string_std__string_t getParams() {
    return new SWIGTYPE_p_std__mapT_std__string_std__string_t(uscxmlNativeJavaJNI.InvokeRequest_params_get(swigCPtr, this), true);
  }

  public void setContent(SWIGTYPE_p_std__string value) {
    uscxmlNativeJavaJNI.InvokeRequest_content_set(swigCPtr, this, SWIGTYPE_p_std__string.getCPtr(value));
  }

  public SWIGTYPE_p_std__string getContent() {
    return new SWIGTYPE_p_std__string(uscxmlNativeJavaJNI.InvokeRequest_content_get(swigCPtr, this), true);
  }

  public static InvokeRequest fromXML(SWIGTYPE_p_std__string xmlString) {
    return new InvokeRequest(uscxmlNativeJavaJNI.InvokeRequest_fromXML(SWIGTYPE_p_std__string.getCPtr(xmlString)), true);
  }

  public SWIGTYPE_p_Arabica__DOM__DocumentT_std__string_t toDocument() {
    return new SWIGTYPE_p_Arabica__DOM__DocumentT_std__string_t(uscxmlNativeJavaJNI.InvokeRequest_toDocument(swigCPtr, this), true);
  }

  public SWIGTYPE_p_std__string toXMLString() {
    return new SWIGTYPE_p_std__string(uscxmlNativeJavaJNI.InvokeRequest_toXMLString(swigCPtr, this), true);
  }

  public InvokeRequest() {
    this(uscxmlNativeJavaJNI.new_InvokeRequest(), true);
  }

}
