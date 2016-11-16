#!/usr/bin/perl -w

#./analyze_tests.pl \
# w3c pml.topml pml.toc pml.tobin pml.verify \
#|awk '{printf("%f\n", ($2 + $3 + $4)); }' \
#|sort -rn \
#|gnuplot -e "set term png;p '-' u 0:1" > test.png

use strict;
use File::Spec;
use File::Basename;
use Data::Dumper;

my $toBaseDir = File::Spec->canonpath(dirname($0));
my $outDir   = File::Spec->catfile($toBaseDir, 'graphs');
my $testResultFile;

my @dataQuery;

# iterate given arguments and populate $dataQuery
foreach my $argnum (0 .. $#ARGV) {
	if ($argnum == $#ARGV) {
		if (-f $ARGV[$argnum]) {
			$testResultFile = $ARGV[$argnum];
			last;
		}
		if (-f File::Spec->catfile($toBaseDir, $ARGV[$argnum])) {
			$testResultFile = File::Spec->catfile($toBaseDir, $ARGV[$argnum]);
			last;
		}
	}
	push(@dataQuery, \[split('\.', $ARGV[$argnum])]);
}

if (!$testResultFile) {
	$testResultFile = File::Spec->catfile($toBaseDir, "../../build/cli/Testing/Temporary/LastTest.log");
}

print STDERR "Using log file from:\n\t$testResultFile\n";

open(FILE, $testResultFile) or die $!;
mkdir($outDir) or die($!) if (! -d $outDir);

my $test;
my $block;
my $currTest;
my $testIndex = 0;

$/ = '-' x 58 . "\n";

while ($block = <FILE>) {
	chomp($block);
		
	# Test Preambel ========
	if ($block =~ 
		/
			\n?
			(\d+)\/(\d+)\sTesting:\s(.*)\n
			(\d+)\/(\d+)\sTest:\s(.*)\n
		/x ) {
		$currTest = $3;
		$test->{$currTest}->{'name'} = $currTest;
		$test->{$currTest}->{'number'} = $1;
		$test->{$currTest}->{'total'} = $2;
		$test->{$currTest}->{'index'} = $testIndex++;
		
		if ($currTest =~ /test(\d+\w?)\.scxml$/) {
			$test->{$currTest}->{'w3c'} = $1;
		}
		
		next;
	}
	
	# Test Epilog ========
	if ($block =~ 
		/
			Test\s(\S+)\.\n
		/x ) {
		$test->{$currTest}->{'status'} = lc($1);
		next;
	}
	
	# Test Duration ========
	if ($block =~ 
		/
			\<end\sof\soutput\>\n
			Test\stime\s\=\s+([\d\.]+)\s(\w+)
		/x ) {
		$test->{$currTest}->{'duration'}->{'total'} = $1;
		$test->{$currTest}->{'duration'}->{'totalUnit'} = $2;
		# next; - no next as this is part of the actual test output we need to scan below
	}
	
	# Performance ========
	if ($block =~ 
		/
			(\d+)\siterations\n
			([\d\.]+)\sms\sin\stotal\n
			([\d\.]+)\sms\sper\sexecution\n
			(\d+)\smicrosteps\sper\siteration\n
			([\d\.]+)\sms\sper\smicrostep\n
			([\d\.]+)\sms\sin\sdatamodel\n
			([\d\.]+)\sms\sper\smicrostep\s\\wo\sdatamodel\n
		/x ) {
			$test->{$currTest}->{'benchmark'}->{'iterations'} = $1;
			$test->{$currTest}->{'benchmark'}->{'total'} = $2;
			$test->{$currTest}->{'benchmark'}->{'perExecution'} = $3;
			$test->{$currTest}->{'benchmark'}->{'mirosteps'} = $4;
			$test->{$currTest}->{'benchmark'}->{'perMicrostep'} = $5;
			$test->{$currTest}->{'benchmark'}->{'inDataModel'} = $6;
			$test->{$currTest}->{'benchmark'}->{'inMicrostep'} = $7;
	}

	if ($block =~ /Size\sof\scompiled\sunit:\s(\d+)/x ) {
			$test->{$currTest}->{'benchmark'}->{'size'} = $1;
	}

	if ($block =~ /Size\sof\scompiled\sunit\soptimized\sfor\sspeed:\s(\d+)/x ) {
			$test->{$currTest}->{'benchmark'}->{'sizeFast'} = $1;
	}

	if ($block =~ /Size\sof\scompiled\sunit\soptimized\sfor\ssize:\s(\d+)/x ) {
			$test->{$currTest}->{'benchmark'}->{'sizeSmall'} = $1;
	}
	
	# Minimization ========
	# print $block;

	if ($block =~ 
		/
			Number\sof\selements\sbefore\sreduction:\s(\d+)
		/x ) {
		$test->{$currTest}->{'min'}->{'before'} = $1;
		if ($block =~ 
			/
				Number\sof\selements\safter\sreduction:\s(\d+)
			/x ) {
			$test->{$currTest}->{'min'}->{'after'} = $1;
		}
	}
	
	# Flattening ========

	if ($block =~ 
		/
			Number\sof\selements\sbefore\sflattening:\s(\d+)
		/x ) {
		$test->{$currTest}->{'flat'}->{'before'} = $1;
		if ($block =~ 
			/
				Number\sof\selements\safter\sflattening:\s(\d+)
			/x ) {
			$test->{$currTest}->{'flat'}->{'after'} = $1;
		}
	}
	
	# New Promela Tests ========
	if ($block =~ 
	/ 
		uscxml-transform[^\n]+tpml
	/x ) {

		if ($block =~ 
		/
			\nreal\s+(\d+.?\d+)
			\nuser\s+(\d+.?\d+)
			\nsys\s+(\d+.?\d+)
			\n--\stime\sfor\stransforming\sto\spromela
		/x ) {
			$test->{$currTest}->{'pml'}->{'toPML'} = $1;
		}

		if ($block =~ 
		/
			\nreal\s+(\d+.?\d+)
			\nuser\s+(\d+.?\d+)
			\nsys\s+(\d+.?\d+)
			\n--\stime\sfor\stransforming\sto\sc
		/x ) {
			$test->{$currTest}->{'pml'}->{'toC'} = $1;
		}

		if ($block =~ 
		/
			\nreal\s+(\d+.?\d+)
			\nuser\s+(\d+.?\d+)
			\nsys\s+(\d+.?\d+)
			\n--\stime\sfor\stransforming\sto\sbin
		/x ) {
			$test->{$currTest}->{'pml'}->{'toBIN'} = $1;
		}

		if ($block =~ 
		/
			\nreal\s+(\d+.?\d+)
			\nuser\s+(\d+.?\d+)
			\nsys\s+(\d+.?\d+)
			\n--\stime\sfor\sverification
		/x ) {
			$test->{$currTest}->{'pml'}->{'verify'} = $1;
		}

		if ($block =~ /State-vector (\d+) byte, depth reached (\d+), errors: (\d+)/) {
			$test->{$currTest}->{'pml'}->{'states'}->{'stateSize'} = $1;
			$test->{$currTest}->{'pml'}->{'states'}->{'depth'} = $2;
			$test->{$currTest}->{'pml'}->{'states'}->{'errors'} = $3;
		}
		if ($block =~ 
			/
				\s+(\d+)\sstates,\sstored\s\((\d+)\svisited\)\n
				\s+(\d+)\sstates,\smatched\n
				\s+(\d+)\stransitions\s\(=\svisited\+matched\)\n
				\s+(\d+)\satomic\ssteps\n
				hash\sconflicts:\s+(\d+)\s\(resolved\)
			/x ) {
			$test->{$currTest}->{'pml'}->{'states'}->{'stateStored'} = $1;
			$test->{$currTest}->{'pml'}->{'states'}->{'stateVisited'} = $2;
			$test->{$currTest}->{'pml'}->{'states'}->{'stateMatched'} = $3;
			$test->{$currTest}->{'pml'}->{'states'}->{'transitions'} = $4;
			$test->{$currTest}->{'pml'}->{'states'}->{'atomicSteps'} = $5;
			$test->{$currTest}->{'pml'}->{'hashConflicts'} = $6;
		}
		
		if ($block =~ 
			/
				\s+([\d\.]+)\sequivalent\smemory\susage\sfor\sstates.*
				\s+([\d\.]+)\sactual\smemory\susage\sfor\sstates\n
				\s+([\d\.]+)\smemory\sused\sfor\shash\stable\s\(-w(\d+)\)\n
				\s+([\d\.]+)\smemory\sused\sfor\sDFS\sstack\s\(-m(\d+)\)
				\s+([\d\.]+)\stotal\sactual\smemory\susage
			/x ) {
			$test->{$currTest}->{'pml'}->{'memory'}->{'states'} = $1;
			$test->{$currTest}->{'pml'}->{'memory'}->{'actual'} = $2;
			$test->{$currTest}->{'pml'}->{'memory'}->{'hashTable'} = $3;
			$test->{$currTest}->{'pml'}->{'memory'}->{'hashLimit'} = $4;
			$test->{$currTest}->{'pml'}->{'memory'}->{'dfsStack'} = $5;
			$test->{$currTest}->{'pml'}->{'memory'}->{'dfsLimit'} = $6;
			$test->{$currTest}->{'pml'}->{'memory'}->{'total'} = $7;
		}

		if ($block =~ 
			/
				pan:\selapsed\stime\s(.*)\sseconds\n
			/x ) {
			$test->{$currTest}->{'pml'}->{'duration'} = $1;
		}

	}
		
	
	
	# Promela Test ========
	if ($block =~ 
		/
			Approximate\sComplexity:\s(\d+)\n
			Approximate\sActive\sComplexity:\s(\d+)\n
		/x ) {
		$test->{$currTest}->{'flat'}->{'cmplx'}->{'appr'} = $1;
		$test->{$currTest}->{'flat'}->{'cmplx'}->{'apprActv'} = $2;
		
		if ($block =~ 
			/
				Actual\sComplexity:\s(\d+)\n
				Actual\sActive\sComplexity:\s(\d+)\n
				Internal\sQueue:\s(\d+)\n
				External\sQueue:\s(\d+)\n
			/x ) {
			$test->{$currTest}->{'flat'}->{'cmplx'}->{'actual'} = $1;
			$test->{$currTest}->{'flat'}->{'cmplx'}->{'actualActv'} = $2;
			$test->{$currTest}->{'flat'}->{'queue'}->{'internal'} = $3;
			$test->{$currTest}->{'flat'}->{'queue'}->{'external'} = $4;
		}
		
		if ($block =~ /State-vector (\d+) byte, depth reached (\d+), errors: (\d+)/) {
			$test->{$currTest}->{'pml'}->{'states'}->{'stateSize'} = $1;
			$test->{$currTest}->{'pml'}->{'states'}->{'depth'} = $2;
			$test->{$currTest}->{'pml'}->{'states'}->{'errors'} = $3;
		}
		if ($block =~ 
			/
				\s+(\d+)\sstates,\sstored\s\((\d+)\svisited\)\n
				\s+(\d+)\sstates,\smatched\n
				\s+(\d+)\stransitions\s\(=\svisited\+matched\)\n
				\s+(\d+)\satomic\ssteps\n
				hash\sconflicts:\s+(\d+)\s\(resolved\)
			/x ) {
			$test->{$currTest}->{'pml'}->{'states'}->{'stateStored'} = $1;
			$test->{$currTest}->{'pml'}->{'states'}->{'stateVisited'} = $2;
			$test->{$currTest}->{'pml'}->{'states'}->{'stateMatched'} = $3;
			$test->{$currTest}->{'pml'}->{'states'}->{'transitions'} = $4;
			$test->{$currTest}->{'pml'}->{'states'}->{'atomicSteps'} = $5;
			$test->{$currTest}->{'pml'}->{'hashConflicts'} = $6;
		}
		
		if ($block =~ 
			/
				\s+([\d\.]+)\sequivalent\smemory\susage\sfor\sstates.*
				\s+([\d\.]+)\sactual\smemory\susage\sfor\sstates\n
				\s+([\d\.]+)\smemory\sused\sfor\shash\stable\s\(-w(\d+)\)\n
				\s+([\d\.]+)\smemory\sused\sfor\sDFS\sstack\s\(-m(\d+)\)
				\s+([\d\.]+)\stotal\sactual\smemory\susage
			/x ) {
			$test->{$currTest}->{'pml'}->{'memory'}->{'states'} = $1;
			$test->{$currTest}->{'pml'}->{'memory'}->{'actual'} = $2;
			$test->{$currTest}->{'pml'}->{'memory'}->{'hashTable'} = $3;
			$test->{$currTest}->{'pml'}->{'memory'}->{'hashLimit'} = $4;
			$test->{$currTest}->{'pml'}->{'memory'}->{'dfsStack'} = $5;
			$test->{$currTest}->{'pml'}->{'memory'}->{'dfsLimit'} = $6;
			$test->{$currTest}->{'pml'}->{'memory'}->{'total'} = $7;
		}

		if ($block =~ 
			/
				pan:\selapsed\stime\s(.*)\sseconds\n
			/x ) {
			$test->{$currTest}->{'pml'}->{'duration'} = $1;
		}

		if ($block =~ 
			/
				real\s+([\d\.]+)\n
				user\s+([\d\.]+)\n
				sys\s+([\d\.]+)\n
				--\stime\sfor\stransforming\sto\spromela\n
			/x ) {
			$test->{$currTest}->{'duration'}->{'toPML'} = $1;
		}

		if ($block =~ 
			/
				real\s+([\d\.]+)\n
				user\s+([\d\.]+)\n
				sys\s+([\d\.]+)\n
				--\stime\sfor\stransforming\sto\sc\n
			/x ) {
			$test->{$currTest}->{'duration'}->{'toC'} = $1;
		}

		if ($block =~ 
			/
				real\s+([\d\.]+)\n
				user\s+([\d\.]+)\n
				sys\s+([\d\.]+)\n
				--\stime\sfor\stransforming\sto\sbinary\n
			/x ) {
			$test->{$currTest}->{'duration'}->{'toBin'} = $1;
		}

		if ($block =~ 
			/
				real\s+([\d\.]+)\n
				user\s+([\d\.]+)\n
				sys\s+([\d\.]+)\n
				--\stime\sfor\sverification\n
			/x ) {
			$test->{$currTest}->{'duration'}->{'toVerif'} = $1;
		}
		
		next;
	}
	
}
close(FILE);

if (@dataQuery > 0) {
	while (my ($name, $data) = each $test) {
		my $seperator = "";
		foreach (@dataQuery) {
			my $currVal = $data;
			my @query = @${$_};
			foreach (@query) {
				my $dataKey = $_;
				if (defined($currVal->{$dataKey})) {
					$currVal = $currVal->{$dataKey};
				} else {
					print STDERR "no key $dataKey in structure:\n" . Dumper($currVal);
					$currVal = "N/A";
					last;
				}
			}
			print $seperator . $currVal;
			$seperator = ", ";
		}
		print "\n";
	}
} else {
	while (my ($name, $data) = each $test) {
		# get one $data into scope
		print "Available Queries:\n";

		sub dumpQueries() {
			my $structure = shift;
			my $path = shift || "";
			while (my ($name, $data) = each $structure) {
				if (ref(\$data) eq "SCALAR") {
					print "\t" . $path . $name . "\n";
				} else {
					&dumpQueries($data, $path . $name . ".");
				}
			}
		}
		&dumpQueries($data);
		exit;
	}
}

