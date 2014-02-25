#!/bin/sh

if [ $# -lt 1 ]
then
        echo "Usage : $0 TimCommandID Write(1)/Read(0)"
        exit
fi

case "$1" in

-1) echo "Initializing Interpreter"
	ping 127.0.0.1
    ;;
0)  echo "Sending command $1"
	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -0 -1 -t0 -o4 -p 1502 -r1 -c1 127.0.0.1 1
	else
		/usr/local/bin/modpoll -0 -1 -t0 -o4 -p 1502 -r2 -c1 127.0.0.1
	fi
    ;;
1)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"		
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r56 -c84 127.0.0.1
	fi
    ;;
2)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"		
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r305 -c23 127.0.0.1
	fi
   ;;
3)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"		
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r549 -c114 127.0.0.1
	fi
   ;;
4)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"		
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r893 -c1 127.0.0.1
	fi
   ;;
5)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"		
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r894 -c23 127.0.0.1
	fi
   ;;
6)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1029 -c1 127.0.0.1 2158
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r917 -c29 127.0.0.1
	fi
   ;;
7)  echo  "Sending command $1"
	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1316 -c1 127.0.0.1 878
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1207 -c74 127.0.0.1
	fi
   ;;
8)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1587 -c1 127.0.0.1 1
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1577 -c23 127.0.0.1
	fi
   ;;
9)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"	
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1699 -c29 127.0.0.1
	fi
   ;;
10)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		echo "Write Mode is Not Supported"	
	else
		/usr/local/bin/modpoll -0 -1 -t4 -o4 -p 1502 -r1989 -c32 127.0.0.1
	fi
   ;;
*) echo "Signal number $1 is not supported"
   ;;
esac

# comando 3 read

