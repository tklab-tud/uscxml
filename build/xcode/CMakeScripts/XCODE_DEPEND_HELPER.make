# DO NOT EDIT
# This makefile makes sure all linkable targets are
# up-to-date with anything they link to
default:
	echo "Do not invoke directly"

# For each target create a dummy rule so the target does not have to exist
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a:
/opt/local/lib/libxml2.dylib:
/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a:
/usr/local/lib/libarabica.a:
/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a:
/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a:
/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a:
/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a:
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a:
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a:
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a:


# Rules to remove targets that are older than anything to which they
# link.  This forces Xcode to relink the targets from scratch.  It
# does not seem to check these dependencies itself.
PostBuild.uscxml.Debug:
PostBuild.test-apache-commons.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-apache-commons
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-apache-commons:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-apache-commons


PostBuild.test-communication.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-communication
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-communication:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-communication


PostBuild.test-ecmascript-v8.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-ecmascript-v8
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-ecmascript-v8:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-ecmascript-v8


PostBuild.test-eventdelay.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-eventdelay
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-eventdelay:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-eventdelay


PostBuild.test-execution.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-execution
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-execution:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-execution


PostBuild.test-predicates.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-predicates
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-predicates:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Debug/test-predicates


PostBuild.uscxmlNativeJava.Debug:
PostBuild.uscxml.Debug: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Debug/libuscxmlNativeJava.jnilib
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Debug/libuscxmlNativeJava.jnilib:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Debug/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Debug/libuscxmlNativeJava.jnilib


PostBuild.uscxml.Release:
PostBuild.test-apache-commons.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-apache-commons
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-apache-commons:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-apache-commons


PostBuild.test-communication.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-communication
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-communication:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-communication


PostBuild.test-ecmascript-v8.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-ecmascript-v8
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-ecmascript-v8:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-ecmascript-v8


PostBuild.test-eventdelay.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-eventdelay
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-eventdelay:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-eventdelay


PostBuild.test-execution.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-execution
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-execution:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-execution


PostBuild.test-predicates.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-predicates
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-predicates:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/Release/test-predicates


PostBuild.uscxmlNativeJava.Release:
PostBuild.uscxml.Release: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Release/libuscxmlNativeJava.jnilib
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Release/libuscxmlNativeJava.jnilib:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/Release/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/Release/libuscxmlNativeJava.jnilib


PostBuild.uscxml.MinSizeRel:
PostBuild.test-apache-commons.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-apache-commons
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-apache-commons:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-apache-commons


PostBuild.test-communication.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-communication
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-communication:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-communication


PostBuild.test-ecmascript-v8.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-ecmascript-v8
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-ecmascript-v8:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-ecmascript-v8


PostBuild.test-eventdelay.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-eventdelay
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-eventdelay:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-eventdelay


PostBuild.test-execution.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-execution
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-execution:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-execution


PostBuild.test-predicates.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-predicates
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-predicates:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/MinSizeRel/test-predicates


PostBuild.uscxmlNativeJava.MinSizeRel:
PostBuild.uscxml.MinSizeRel: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/MinSizeRel/libuscxmlNativeJava.jnilib
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/MinSizeRel/libuscxmlNativeJava.jnilib:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/MinSizeRel/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/MinSizeRel/libuscxmlNativeJava.jnilib


PostBuild.uscxml.RelWithDebInfo:
PostBuild.test-apache-commons.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-apache-commons
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-apache-commons:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-apache-commons


PostBuild.test-communication.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-communication
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-communication:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-communication


PostBuild.test-ecmascript-v8.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-ecmascript-v8
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-ecmascript-v8:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-ecmascript-v8


PostBuild.test-eventdelay.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-eventdelay
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-eventdelay:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-eventdelay


PostBuild.test-execution.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-execution
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-execution:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-execution


PostBuild.test-predicates.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-predicates
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-predicates:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/test/RelWithDebInfo/test-predicates


PostBuild.uscxmlNativeJava.RelWithDebInfo:
PostBuild.uscxml.RelWithDebInfo: /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/RelWithDebInfo/libuscxmlNativeJava.jnilib
/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/RelWithDebInfo/libuscxmlNativeJava.jnilib:\
	/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/RelWithDebInfo/libuscxml.a\
	/opt/local/lib/libxml2.dylib\
	/Users/sradomski/Documents/TK/Code/glog/.libs/libglog.a\
	/usr/local/lib/libarabica.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent.a\
	/Users/sradomski/Documents/TK/Code/libevent/.libs/libevent_pthreads.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_base.a\
	/Users/sradomski/Documents/TK/Code/v8/out/native/libv8_snapshot.a
	/bin/rm -f /Users/sradomski/Documents/TK/Code/uscxml/build/xcode/src/bindings/swig/java/RelWithDebInfo/libuscxmlNativeJava.jnilib


