#!/bin/sh

if [ $# -lt 1 ]
then
        echo "Usage : $0 <TimCommandID> <1(Write)/0(Read)> <IP Address>" 
        exit
fi

case "$1" in

-1) echo "Initializing Interpreter"
<<<<<<< HEAD
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
=======
#	export LD_PRELOAD="/usr/local/lib/libmodbus.so.5"
#	pkill -f /home/sunkiss/_Projects/xmlBridgeCPP/GW-MES2TIM
	ping 10.1.30.150
    ;;
0)  echo "Sending command $1"
#	pkill -f /usr/bin/nc
	if [ "$2" -eq "1" ] ; then
#		(/usr/bin/cat write0.xml | /usr/bin/nc -l -v -p 3000 >/dev/null) &
#		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t0 -r4 10.1.30.150	1
	else
#		(/usr/bin/cat read0.xml | /usr/bin/nc -l -v -p 3000 >/dev/null) &
#		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t0 -r4 10.1.30.150
	fi
    ;;
1)  echo  "Sending command $1"
#	pkill -f /usr/bin/nc
>>>>>>> e5771fa48d1b58753ba2d48165fd219ce77e83ec
    	if [ "$2" -eq "1" ] ; then
		sleep 1				
<<<<<<< HEAD
	else
		/usr/local/bin/modpoll -1 -c 8 -o 4 -p 502 -t0 -r14 $3
=======
		#/usr/local/bin/modpoll -1 -c 4 -o 4 -p 501 -t0 -r14 10.1.30.150	1 0 1 0
	else
#		(/usr/bin/cat read1.xml | /usr/bin/nc -l -v -p 3000 >/dev/null) &
#		sleep 1
		/usr/local/bin/modpoll -1 -c 8 -o 4 -p 501 -t0 -r14 10.1.30.150
>>>>>>> e5771fa48d1b58753ba2d48165fd219ce77e83ec
	fi
    ;;
2)  echo  "Sending command $1"
    ;;
3)  echo  "Sending command $1"
<<<<<<< HEAD
    	if [ "$2" -eq "1" ] ; then
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r41 $3 62000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r45 $3 254
		/usr/local/bin/modpoll -1 -c 2 -o 4 -p 502 -t4 -r49 $3 254 223
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t0 -r54 $3 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r78 $3 61000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r84 $3 48
	else
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 502 -t4 -r41 $3
=======
#	pkill -f /usr/bin/nc
    	if [ "$2" -eq "1" ] ; then
#		(/usr/bin/cat write3.xml | /usr/bin/nc -l -v -p 3000 >/dev/null) &
#		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t4 -r41 10.1.30.150 62000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t4 -r45 10.1.30.150 254
		/usr/local/bin/modpoll -1 -c 2 -o 4 -p 501 -t4 -r49 10.1.30.150 254 223
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t0 -r54 10.1.30.150 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t4 -r78 10.1.30.150 61000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t4 -r84 10.1.30.150 48
#	else
#		(/usr/bin/cat read3.xml | /usr/bin/nc -l -v -p 3000 >/dev/null) &
#		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 501 -t4 -r41 10.1.30.150
>>>>>>> e5771fa48d1b58753ba2d48165fd219ce77e83ec
	fi
   ;;
*) echo "Signal number $1 is not supported"
   ;;
esac

# comando 3 read

