set clkl [list]
lappend clkl "$clk"
set num_added [ gtkwave::addSignalsFromList $clkl ]
