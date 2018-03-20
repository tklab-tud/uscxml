========================================================================
   
                    Invoke examples
    
========================================================================

This directory contains three folders namely (1) Invoker_generator (2) calc (3) ftp.
calc and ftp are examples to demonstrate the communication between a Contiki application modeled in SCXML and other existing contiki applications. We will show the process by taking the example of calc application but same can applied for ftp application.

For generating the files necessary for communication, we are going to use the tool in directory Invoker_generator.
Please follow the steps below: 
1) Build the tool Invoker_generator using GNU make.
2) Generate the files required for the communication by executing the following command: 

>USCXML_Contiki_Inv_Gen.exe contiki/apps/calc/calc.c

This command will generate four files, please re-place the files in the directories mentioned below: 


calc.c: This file is very similar to the input file except that the generated header file is included at the top that is the statement #include calc.h is added on top. Also, the statement AUTOSTART_PROCESSES(&calc_process); is removed from the file. This is required as we do not want calc_process to be auto-started when Contiki is loaded but rather, we want the calc process to be started only when our IoT application encounters an invocation element of type "Contiki_calc". This file should be re-placed at its original location which is [Contiki_dir]/apps/calc/ in our example.

calc.h: This is a header file that declares the process that we are invoking (calc_process in our example). This file needs to be placed alongside the process source file that contains the definition of the process which is [Contiki_dir]/apps/calc/ in our example.

contiki_calc_invoker.h: This is a header file that declares an invoke class in the same syntax as required by uSCXML interpreter’s factory class to register an invoke for any type. This file must be placed in our application’s invoker directory which is ./calc/invokers. 

Contiki_calc_invoker.cpp: This file contains the definition for what was declared in the header file. It contains the definition of the invoke / uninvoke method declared in calc.h. The calls from an invoke method is redirected to the invoke() function defined in this class. We must register our invoker with the factory class of uSCXML before we start using this invoke type. This is done at the very beginning of the process in our scaffolding. This file must be placed in our application’s invoker directory which is ./calc/invokers.

/////////////////////////////////////////////////////////////////////////////
