set loadpath \
	'~/Documents/TK/Code/gnuplot-colorbrewer/diverging' \
	'~/Documents/TK/Code/gnuplot-colorbrewer/qualitative' \
	'~/Documents/TK/Code/gnuplot-colorbrewer/sequential'

load 'Dark2.plt'

set datafile missing "NA"

# set style line 1 lc rgb '#1B9E77' lw 1.5 pt 5 ps 0.2
# set style line 2 lc rgb '#1B9E77' lw 1.5 pt 5 ps 0.2 dt 4
# set style line 3 lc rgb '#D95F02' lw 1.5 pt 5 ps 0.2
# set style line 4 lc rgb '#D95F02' lw 1.5 pt 5 ps 0.2 dt 4
# set style line 5 lc rgb '#7570B3' lw 1.5 pt 5 ps 0.2
# set style line 6 lc rgb '#7570B3' lw 1.5 pt 5 ps 0.2 dt 4
# set style line 7 lc rgb '#E7298A' lw 1.5 pt 5 ps 0.2
# set style line 8 lc rgb '#E7298A' lw 1.5 pt 5 ps 0.2 dt 4
# set style line 20 lc rgb '#666666' lw 1.5 pt 5 ps 0.2 dt 4

set terminal pdf font 'Verdana,10'
# set termoption dash
# set palette negative
set termoption enhanced

# deemphasize border
set style line 11 lc rgb '#505050' lt 4
set border 11 back ls 11

# small grid
set style line 12 lc rgb '#808080' lt 0 lw 1
set grid ytics back ls 12

set xtics nomirror out
# set ytics nomirror

set xtics border rotate by -45
