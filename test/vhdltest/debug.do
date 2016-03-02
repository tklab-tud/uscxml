# window setup
view structure
view signals
view wave

# wave setup
add wave -noupdate -divider -height 20 Inputs
add wave -position insertpoint  \
sim:/tb/dut/clk \
sim:/tb/dut/rst_i \
sim:/tb/dut/en

add wave -noupdate -divider -height 20 Outputs
add wave -position insertpoint  \
sim:/tb/dut/state_active_*_o \
sim:/tb/dut/completed_o 

add wave -noupdate -divider -height 20 System
add wave -position insertpoint  \
sim:/tb/dut/stall \
sim:/tb/dut/rst \
sim:/tb/dut/spontaneous_en \
sim:/tb/dut/optimal_transition_set_combined_sig

add wave -noupdate -divider -height 20 Entry_Set
add wave -position insertpoint  \
sim:/tb/dut/in_entry_set_*_sig \
sim:/tb/dut/in_complete_entry_set_*_sig 

add wave -noupdate -divider -height 20 Exit_Set
add wave -position insertpoint  \
sim:/tb/dut/in_exit_set_*_sig 

add wave -noupdate -divider -height 20 Transition_Set
add wave -position insertpoint  \
sim:/tb/dut/in_optimal_transition_set_*_sig 

add wave -noupdate -divider -height 20 Event
add wave -position insertpoint  \
sim:/tb/dut/*event* 

add wave -noupdate -divider -height 20 ALL
add wave -position insertpoint  \
sim:/tb/dut/*

# run simulation
run 500 ns
