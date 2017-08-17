========================================================================
   
                    Dining philosopher Contiki Project Overview
    
========================================================================

(PS: If you already know about the problem, you can skip overview and jump directly to pre-requisite for building this Contiki application for dining philosopher problem)

Five philosophers spend their time thinking and eating spaghetti(the tasks). They eat at a round table
with five individual seats. For eating each philosopher needs two forks (the resources). There are five forks
on the table, one left and one right of each seat. When a philosopher cannot grab both forks it sits and
waits. Eating takes random time, then the philosopher puts the forks down and leaves the dining room.
After spending some random time thinking about the nature of the universe, he again becomes hungry,
and the circle repeats itself. The problem was designed to illustrate the challenges of avoiding deadlock, a system state in which no
progress is possible.

This Contiki aplication shows the problem with following behaviour for one philosopher: 
1) Think until you become hungry.
2) Once hungry ask for left and right fork.
3) if left fork acquired, wait until the right fork is available; when it is, pick it up;
4) if right fork acquired, wait until the left fork is available; when it is, pick it up;
5) when both forks are held, eat for a fixed amount of time;
6) then, put both forks down;
7) repeat from the beginning

Above behaviour was modelled in SCXML (\apps\contiki\dining_philosopher\dp\scxml) then transpiled to ANSI C (\apps\contiki\dining_philosopher\dp\input) using uscxml transpilation.
When run, this problem will fail because of the inherent deadlock present in the problem. Deadlock free solution in form of contiki application is provided in \apps\contiki\dining_philosopher\dp_solution directory.


---------------------------Pre-requisite-------------------------------- 
1) User is able to successfully build one of the examples provided by Contiki for TARGET=win32 or TARGET=native(Default).
2) User has already made Contiki changes as mentioned in '\apps\contiki\prerequisite_contiki_changes\README.MD'
---------------------------Pre-requisite End----------------------------


---------------------------Build and Execution steps--------------------
Please follow below steps exactly to build Dining philosopher Contiki application.

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


/////////////////////////////////////////////////////////////////////////////
