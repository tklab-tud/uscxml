========================================================================
   
                    uscxml Contiki Project Overview
    
========================================================================

This project is to demonstrate binding between uscxml, which is an interpreter and transpiler for SCXML and Contiki, which is operating system for IoT. This project contains 5 examples to demonstrate the same with each example serving a different purpose. 

1) Dining Philosopher problem(#1) and Dining philosopher(#2) solution: This example shows applicability to computer science problem. We define problem in SCXML, transpile using uscxml then create Contiki scaffolding and finally run it in Contiki node win32 and native. Spin output and transpiled PROMELA input for verification check of existing progress cycle is also given in directory /dining_philosopher/dp/formal_verification and /dining_philosopher/dp_solution/formal_verification.

3) SCXML IRP Tests (#3): This directory contains a general Contiki scaffolding to run 170/233 IRP test mentioned by SCXML recommendation. We only provide 1 example of IRP tests in this solution. However, user can execute any of the SCXML IRP test (out of 170 tests) by copying a test into \apps\contiki\SCXML_IRP_tests\scxml directory then transpiling it onto ANSI-C using uscxml transpiler and place the result in input (\apps\contiki\dining_philosopher\dp_solution\input) directory. 
Also, Make sure to edit 'IRP_tests.cpp' to include this test instead of before mentioned IRP test.

4) Invoke examples (CALC(#4) & FTP(#5)): Contains an approach that provides the communication mechanism between other Contiki applications and SCXML-based Contiki application.
Invoker_generator is a solution that auto-generates necessary files required for communication. Calc and FTP are examples that shows this communication. 

----------------Build Steps-------------------------------------------

1) Make changes to Contiki build system as mentioned in 'prerequisite_contiki_changes/README.MD' directory.
2) To execute a specific example, follow steps given in any of the example application README.MD file. (For e.g. one such README file is present in directory dining_philosopher/dp/README.MD)
