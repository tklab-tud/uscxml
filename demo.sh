#!/bin/sh


if [ $# -lt 2 ]
then
        echo "Usage : $0 TimCommandID w/r"
        exit
fi

case "$1" in

0)  echo "Sending command $1"
	if ["$2" == "w" ] ; then
		nc -l -v -p 3200 < write0.xml &
		modpoll -1 -c 1 -o 4 -p 1501 -t0 -r4 127.0.0.1	1
	else
		nc -l -v -p 3200 < read3.xml &
		modpoll -1 -c 1 -o 4 -p 1501 -t0 -r4 127.0.0.1
	fi
    ;;
1)  echo  "Sending command $1"
    	if ["$2" == "w" ] ; then
		nc -l -v -p 3200 < write1.xml &
		modpoll -1 -c 4 -o 4 -p 1501 -t0 -r14 127.0.0.1	1 0 1 0
	else
		nc -l -v -p 3200 < read1.xml &
		modpoll -1 -c 8 -o 4 -p 1501 -t0 -r14 127.0.0.1
	fi
    ;;
2)  echo  "Sending command $1"
  
    ;;
3)  echo  "Sending command $1" 
	if ["$2" == "w" ] ; then
		nc -l -v -p 3200 < write3.xml &
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r41 127.0.0.1 254
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r45 127.0.0.1 254
		modpoll -1 -c 2 -o 4 -p 1501 -t4 -r49 127.0.0.1 254 223
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r54 127.0.0.1 254
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r78 127.0.0.1 255
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r84 127.0.0.1 255
	else
		nc -l -v -p 3200 < read3.xml &
		modpoll -1 -c 1 -o 4 -p 1501 -t4 -r41 127.0.0.1
	fi
   ;;
*) echo "Signal number $1 is not supported"
   ;;
esac

# comando 3 read

