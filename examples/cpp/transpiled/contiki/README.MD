========================================================================
   
                    uSCXML-Contiki binding Project Overview
    
========================================================================

This project is to demonstrate binding between uSCXML, which is an interpreter and transpiler for SCXML and Contiki, which is an operating system for the IoT. This project contains 4 examples to demonstrate the same with each example serving a different purpose. 

1) Dining Philosopher problem( #1) and Dining philosopher deadlock free version (#2): This example shows applicability of SCXML to computer science problems. We define the problem in SCXML, transpile it onto ANSI-C using uSCXML then create a Contiki scaffolding and run it in a Contiki node win32 and native. The SPIN output and the transpiled PROMELA input are for the formal verification check of existing non-progress cycle.

2) Invoke examples (CALC(#3) & FTP(#4)): Contains an approach that provides the communication mechanism between other Contiki applications and SCXML-based Contiki application.
Invoker_generator is a solution that auto-generates necessary files required for communication. Calc and FTP are examples that shows this communication. 

----------------Build Steps-------------------------------------------

1) Make changes to Contiki build system as mentioned in 'prerequisite_contiki_changes/README.MD' directory.
2) To execute a specific example, follow steps given in any of the example application README.MD file. (For e.g. one such README file is present in directory dining_philosopher/dp/README.MD)
