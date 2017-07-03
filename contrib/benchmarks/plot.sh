#!/bin/bash

for bench in Transitions LCCA; do
	rm logs/${bench}.log

	for size in 4 16 64 256 512; do

		for impl in lxsc scion qt scxmlcc apache uscxml-fast uscxml-large; do
			log="logs/${bench}.${size}-${impl}.log"
			if [ ! -s ${log} ]; then
				for i in {1..10}; do
					echo 0, 0 >> $log
				done
			fi

			# prepend implementation name as header
			echo "${impl}.init.${size}", "${impl}" > ${log}.header
			cat ${log} >> ${log}.header

			# analyze values with R
R -q -e "\
library(psych); \
x <- read.csv('${log}.header', head=TRUE, sep=","); \
y <- describe(x, trim=.1, skew=FALSE); \
write.table(y, file = \"${log}.r.csv\", sep=', ');"
			tail -n2 ${log}.r.csv >> logs/${bench}.log
			rm ${log}.header
		done
	done

awk 'NR == 0 || NR % 2 == 0' logs/${bench}.log > logs/${bench}.even
awk 'NR == 0 || NR % 2 == 1' logs/${bench}.log > logs/${bench}.odd
paste -d', ' logs/${bench}.even /dev/null logs/${bench}.odd > logs/${bench}.joined.log

cat << END_GNUPLOT > /tmp/tmp.plot
	set title "Iterations per second for ${bench} Benchmark"

	load 'gnuplot-style.plt'
	set boxwidth 0.25 relative
	set style fill solid 0.25 border
	set key right top
	set offsets 0.5,0.5,0,0

	# set yrange [0:*]
	# set y2range [0:5000]
	# set y2tics nomirror
	set ytics nomirror
	set xtics ("4^2" 0, "16^2" 1, "64^2" 2, "256^2" 3, "512^2" 4)

	set logscale y

	set ylabel "Iterations / sec"
	set xlabel "Complexity"
	# set y2label "Initialization [ms]"

	# see also https://stackoverflow.com/a/25512858/990120
	plot 'logs/${bench}.joined.log' \
		   using (\$0):4:5 every 7::6 with yerrorlines title "uscxml large" axis x1y1, \
		'' using (\$0):4:5 every 7::5 with yerrorlines title "uscxml fast" axis x1y1, \
		'' using (\$0):4:5 every 7::3 with yerrorlines title "scxmlcc" axis x1y1, \
		'' using (\$0):4:5 every 7::4 with yerrorlines title "apache" axis x1y1, \
		'' using (\$0):4:5 every 7::1 with yerrorlines title "scion" axis x1y1, \
		'' using (\$0):4:5 every 7::0 with yerrorlines title "lxsc" axis x1y1, \
		'' using (\$0):4:5 every 7::2 with yerrorlines title "qt" axis x1y1, \
		# '' using (\$0 + 0.1):4:5:xtic(1) every 2::1 with yerrorlines title "Iterations per Second" axis x1y1 #, \
		#'' using (\$0 + 0.1):(\$4):(sprintf("%d", \$4)) every 2::1 with labels notitle offset char 0,1
END_GNUPLOT

	gnuplot /tmp/tmp.plot > "logs/${bench}.pdf"


done;
