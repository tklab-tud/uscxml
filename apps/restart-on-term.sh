#!/bin/sh
# see http://superuser.com/questions/223449/auto-restart-process-on-crash
PROGRAM=$1

RC=1
while [ $RC -ne 0 ]; do
   ./${PROGRAM}
   RC=$?
done
