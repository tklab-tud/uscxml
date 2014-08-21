# uSCXML Developer Overview

The core concept with uSCXML is a state chart and its syntax with regard to valid elements and attributes is given
in the [SCXML specification](http://www.w3.org/TR/scxml/). uSCXML is standards compliant with the exception of 
transitions in history elements which were added rather recently.

## Events

To bring a state-chart to life it needs to receive events. After you instantiated and started SCXML interpreter it
will assume a stable configuration and wait for events. You can send events via <tt>interpreter.receive(Event)</tt>.
An event consists (foremost) of the following attributes:

    std::string name;        // the name of the event
    std::string origin;      // where the event originated
    std::string origintype;  // the type of the event's source
    std::string content;     // literal string content to be space-normalized
    Data data;               // complex, JSON-like event data (conflicts with literal string content)

The first three attributes are available as simple attributes of the datamodel's <tt>_event</tt> object at runtime. If
content is given as a literal string, it will be represented as a space-normalized string in <tt>_event.data</tt>. The
more interesting case is to pass more complex data, in which case, you need to populate the <tt>data</tt> attribute.

### Data

The data attribute, as an instance of the Data class contains a nested tree of arbitrary content and can be used to
pass more complex data structures than space-normalized string literals into the interpreter as <tt>_event.data</tt>.

    std::map<std::string, Data> compound;  // Associative array, key/value pairs
    std::list<Data> array;                 // Simple array of things
    Blob binary;                           // Binary data
    Arabica::DOM::Node<std::string> node;  // A DOM node
    std::string atom;                      // String literal or identifier/value, depending on type
    Type type;                             // [VERBATIM | INTERPRETED], 

Not all datamodels support all types of data, e.g. neither the Prolog nor the Lua datamodel support binary data.
When in doubt, you will have to have a look at the <tt>setEvent(Event)</tt> method of the respective datamodel
implementation. The most complete datamodel's in terms of supported types are those with ECMAScript, supporting
Core Level 2 for XML data and TypedArrays to handle binary data.

When you populate a data object, you can only ever set a single attribute. You can, for example, not set a key in the
compound and an index in the array and expect something meaningful at runtime. For nesting use compound and array, for
scalar data use atom, binary or node.

### DOM Nodes in the Language Bindings

We do not wrap DOM nodes into the target language but pass its serialized XML string representation to be reparsed in
the target languages. There are some examples in the <tt>embedding</tt> directory. In order to pass XML via an event,
the Data class in the language bindings support <tt>setXML()</tt>, which will accept a valid XML string.