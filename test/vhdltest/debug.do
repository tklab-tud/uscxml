# window setup
view structure
view signals
view wave

# wave setup
add wave -noupdate -divider -height 32 Inputs
add wave -position insertpoint  \
sim:/tb/dut/clk \
sim:/tb/dut/rst \
sim:/tb/dut/en

add wave -noupdate -divider -height 32 Outputs
add wave -position insertpoint  \
sim:/tb/dut/state_active_*_o \
sim:/tb/dut/completed_o 

add wave -noupdate -divider -height 32 PRIO
add wave -position insertpoint  \
sim:/tb/dut/stall

add wave -noupdate -divider -height 32 ALL
add wave -position insertpoint  \
sim:/tb/dut/*

# run simulation
run 500 ns
