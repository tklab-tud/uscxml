========================================================================
   
                    Dining philosopher deadlock free version Contiki Project Overview
    
========================================================================

(PS: If you already know about the problem, you can skip overview and jump directly to pre-requisite for building this Contiki application for dining philosopher deadlock free version)

Dining philosopher problem is discussed in \apps\contiki\dining_philosopher\dp\README.MD, here in this Contiki application we implemented one of the possible deadlock free version to dining philosopher problem. In that problem we identified a deadlock in our earlier design of dining philosopher problem. however in application we modified the resource request and allocation pattern that leads to avoidance of following necessary condition for deadlock as mentioned by Coffman ( google coffman necessary condition for deadlock). 

•Hold and Wait Condition:
Requesting process hold already, resources while waiting for requested resources. That is, There must exist a process that is holding a resource already allocated to it while waiting for additional resource that are currently being held by other processes.

•How we avoid it:
In our version, philosophers never hold up a fork and then wait for other resource. They ask for all
required resource at once and it is master who in an atomic step checks if all resources required by
the philosopher are available or not. If they are available it delivers them all to asking philosopher
and denies request of any other philosopher asking for the same resource until it is returned by the
philosopher.

Above behaviour was modelled in SCXML (\apps\contiki\dining_philosopher\deadlock_free\scxml) then transpiled to ANSI C (\apps\contiki\dining_philosopher\dp_deadlock_free\input) using uscxml transpilation.


------------------------------Pre-requisite-----------------------------
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
