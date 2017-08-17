steps to perform to get new invoker. 

(1) generate 4 files using automatic generator.
(2) Copy contiki invoker files to uscxml plugins invoker folder.
(3) Copy contiki specific files to contiki binding invoker folder. 
(4) Add all required invoker specific makefiles directives to uscxml-contiki make file also add source files in invoker folder to PROJECT_SOURCEFILES variable in uscxml-contiki makefile. --- Can be automated.
(5) include header file in uscxml-c-scaffolding and register invoker. 
(6) include header file in factory.cpp and register invoker. -- Not required
(7) Add define in config.h -- Not required

(8) Add invoker that you want to build into contiki-uscxml app to Makefile.Sourcefiles. Also remove any unused invoker. --- Canbe automated. 