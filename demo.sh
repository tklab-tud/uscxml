#!/bin/sh

if [ $# -lt 1 ]
then
        echo "Usage : $0 TimCommandID Write(1)/Read(0)"
        exit
fi

case "$1" in

-1) echo "Initializing Interpreter"
	pkill -f /home/sunkiss/_Projects/xmlBridgeCPP-build/GW-MES2TIM
	/home/sunkiss/_Projects/xmlBridgeCPP-build/GW-MES2TIM -c ../xmlBridgeCPP/map.csv -x autoware_write.scxml &
    ;;
0)  echo "Sending command $1"
	pkill -f /usr/bin/nc
	if [ "$2" -eq "1" ] ; then
		/usr/bin/nc -l -v -p 3200 < write0.xml &
		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t0 -r4 127.0.0.1	1
	else
		/usr/bin/nc -l -v -p 3200 < read0.xml &
		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t0 -r4 127.0.0.1
	fi
    ;;
1)  echo  "Sending command $1"
	pkill -f /usr/bin/nc
    	if [ "$2" -eq "1" ] ; then
		/usr/bin/nc -l -v -p 3200 < write1.xml &
		sleep 1				
		/usr/local/bin/modpoll -1 -c 4 -o 4 -p 1501 -t0 -r14 127.0.0.1	1 0 1 0
	else
		/usr/bin/nc -l -v -p 3200 < read1.xml &
		sleep 1
		/usr/local/bin/modpoll -1 -c 8 -o 4 -p 1501 -t0 -r14 127.0.0.1
	fi
    ;;
2)  echo  "Sending command $1"
    ;;
3)  echo  "Sending command $1"
	pkill -f /usr/bin/nc
    	if [ "$2" -eq "1" ] ; then
		/usr/bin/nc -l -v -p 3200 < write3.xml &
		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t4 -r41 127.0.0.1 62000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t4 -r45 127.0.0.1 254
		/usr/local/bin/modpoll -1 -c 2 -o 4 -p 1501 -t4 -r49 127.0.0.1 254 223
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t0 -r54 127.0.0.1 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t4 -r78 127.0.0.1 61000
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t4 -r84 127.0.0.1 48
	else
		/usr/bin/nc -l -v -p 3200 < read3.xml &
		sleep 1
		/usr/local/bin/modpoll -1 -c 1 -o 4 -p 1501 -t4 -r41 127.0.0.1
	fi
   ;;
*) echo "Signal number $1 is not supported"
   ;;
esac

# comando 3 read

