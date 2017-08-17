========================================================================
   
                    SCXML IRP Tests Contiki Project Overview
    
========================================================================

(PS: If you already know about SCXML IRP Tests, you can skip overview and jump directly to pre-requisite for building this Contiki application for SCXML IRP tests)

The W3C SCXML Implementation Report Plan (IRP) defines 233 tests of all functional requirements for a compliant interpreter. We created a general Contiki scaffolding that would run an identified set out of these tests after semantically equivalent ANSI-C transpilation. we have checked our scaffolding with a set of 170/233 tests by transpiling onto ANSI-C using uscxml and executed these in a Contiki environment.

------------------------------Pre-requisite-----------------------------
1) User is able to successfully build one of the examples provided by Contiki for TARGET=win32 or TARGET=native(Default).
2) User has already made Contiki changes as mentioned in '\apps\contiki\prerequisite_contiki_changes\README.MD'

---------------------------Pre-requisite End----------------------------


---------------------------Build and Execution steps--------------------
Please follow below steps exactly to build this Contiki application.

1) Edit configure_before_make and provide paths for all fields mentioned in that file. 
2) a) If building for 'TARGET=win32', open visual studio command prompt and execute following command. 
> make TARGET=win32
2) b) If building for TARGET=native, Write following command in terminal.
>make
3) a) If above command completes without any error, execute following command to run dining philosopher for TARGET=win32.
> dining_philosopher.win32 'YOUR_IPV4_ADDRESS'
3) b) For running in TARGET=native, execute following command. (no need to provide ip address in this case) 
>./dining_philosopher.native

---------------------------Build and Execution steps End-----------------


---------------------------Note------------------------------------------

We only provide 1 example of IRP tests in this solution. However, user can execute any of the SCXML IRP test (out of 170 tests) by copying test into \apps\contiki\SCXML_IRP_tests\scxml directory then transpiling it onto ANSI-C using uscxml transpiler and place the result in input (\apps\contiki\dining_philosopher\dp_solution\input) directory. 
Make sure to edit 'IRP_tests.cpp' to include this test instead of before mentioned IRP test.
---------------------------Note End--------------------------------------


/////////////////////////////////////////////////////////////////////////////
