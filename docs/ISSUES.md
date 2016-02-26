# Open Issues

## Ad-hoc extensions are deallocated by their interpreter

If you register any ad-hoc extension with an interpreter, be it in C++ or a language binding, this extension's
instance <emph>belongs</emph> to the interpreter. This means i.e. that (i) the interpreter's destructor will
deallocate the extension instance, (ii) you cannot reuse it for another interpreter and (iii) you may not call
its destructor.

For the language bindings, this means furthermore that you have to call <tt>swigReleaseOwnership()</tt> on the
extension instance to prevent the target language's memory management form calling the instances C++ native
destructor. The destructor can only be called once and the interpreter's destructor will do it.

If allocating additional extension instances per interpreter is expensive, consider using aggregation as a "has a"
relationship with the expensive part.

## Not all exceptions are propagated into the target languages

Only exceptions raised during the following methods are propagated into the target language:

    Interpreter::fromXML
    Interpreter::fromURI
    Interpreter::step
    Interpreter::interpret

If you dig around in the exposed APIs, there are other methods that may raise exceptions (e.g.
<tt>interpreter.getDataModel().eval()</tt>). Be careful when calling these. Ultimately, all exceptions ought to be
propagated into the target language to be handled accordingly. We are currently evaluating different approaches to
do so.

## Where is the Android Port?

When I originally tried to compile the required libraries for uSCXML on Android (libevent, curl, libxml2), it would
not work out of the box and I postponed. If there is a demand for an Android port, I can have another look. uSCXML
itself is written in a subset of C++99 and ought to compile just fine.

## UTF8 support

Currently, we use <tt>std::string</tt> to represent all strings. This is not a problem as e.g. the ECMAScript
data models will just interpret these as character arrays and handle Unicode respectively. Though it is a problem if
you like to use non-ASCII characters e.g. in the <tt>id</tt> attribute of states.

## Performance

The performance of uSCXML depends on many things like the employed data model and the platform it runs on. Using a
MacBook Pro with an Intel i7 @2.4Ghz and the ECMAScript data model (<tt>test/uscxml/test-performance.scxml</tt>), we
achieve about 20.000 events/sec. On a Raspberry Pi, however, only 350 events/sec are achieved.

If performance ought to be increased further, the first place to look would be most likely the employed DOM
implementation, which uses the rather expensive <tt>dynamic_cast</tt> somewhat too liberally. For a real
performance boost, the explicit SCXML DOM representation at runtime might be dropped in favor of some simple
structs representing the states and transitions. This has been no priority for us so far as even 350 events/sec is
plenty for our use-cases.

## What about some code documentation?

Up until recently, the APIs of uSCXML were still subject to rather substantial changes. If there is one thing worse
than no documentation, it is wrong documentation, so we did not document the source. Another stumbling block was the
fact that documentation would not show up in the language bindings.

Both issues are resolved by now: The APIs have not changed substantially in about 8 month and the new version of SWIG
will allow doxygen comments to be show up in various target languages; so we will document somewhen soon.
