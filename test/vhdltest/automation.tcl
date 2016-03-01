# simulation time in ms
echo "step size"
set step 20
# time until simulation will be canceled
echo "timeout after"
set timeout 15000000

proc runSim {} {
   # import the global variable step
   global step
   global timeout
   upvar 0 errorMsg_ errorMsg
   set runtime 0

   # reset simulator
   restart -force -nowave
   add wave *
      set errorMsg "ERROR"

   echo "start simulation"

   # run until state machine is finished
   set err 0
   set completed 0
   while { $err != 1 & $completed != 1 & $runtime < $timeout } {
      run $step ns
      set err [examine -time $runtime -binary /testbench/error_o]
      set completed [examine -time $runtime -binary /testbench/completed_o]
      set runtime [ expr $runtime + $step]
   }

   # if running in gui mode, view results
   view wave

   # export results to cmd line
   if { $runtime == $timeout } {
      echo "TIMEOUT"
   } elseif { $err == 1 } {
      echo "ERROR"
   } else {
      echo "OK"
   }

}

# start simulation
runSim

# exit simulator
exit -force  
