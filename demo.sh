#!/bin/sh

if [ $# -lt 1 ]
then
        echo "Usage : $0 <TimCommandID> <1(Write)/0(Read)> <IP Address>" 
        exit
fi

case "$1" in

-1) echo "Initializing Interpreter"
	ping $3
    ;;
0)  echo "Sending command $1"
	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r4 $3 1
	else
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r4 $3 &
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r4 $3 &
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r4 $3 &
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r4 $3 &
	fi
    ;;
1)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		sleep 1				
	else
		/usr/local/bin/modpoll -1 -c 8 -o 4 -p 502 -t0 -r14 $3
	fi
    ;;
2)  echo  "Sending command $1"
    ;;
3)  echo  "Sending command $1"
    	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r41 $3 62000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r45 $3 254
		/usr/local/bin/modpoll -1 -c 2 -o 4 -p 502 -t4 -r49 $3 254 223
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r54 $3 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r78 $3 61000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r84 $3 48
	else
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r41 $3
	fi
   ;;
*) echo "Signal number $1 is not supported"
   ;;
esac

# comando 3 read

