# DEVELOPING with uSCXML

## Getting Started

When you [built SCXML](@ref building), you have three possibilities to work with SCXML state-charts:

1. Embed the uSCXML interpreter in your program and parse and interpret state-chart documents at runtime. This allows for the most flexibility as the complete SCXML DOM is still available.

2. Transpile SCXML state-charts onto one of the available target languages. These are currently VHDL and ANSI-C with C# and Java as likely additional targets. The benefit of this approach is the reduced footprint at runtime and fewer dependencies.

3. Interpret SCXML documents directly with the `uscxml-browser`.