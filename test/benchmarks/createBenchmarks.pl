#!/usr/bin/perl -w

use strict;
use List::Util qw[min max sum];

use warnings;
no warnings 'recursion';

use Getopt::Long qw(GetOptions);
use Data::Dumper;

my %options = ();

GetOptions(
	\%options,
	"depth-max=i",
	"child-max=i",
	"events-max=i",
	"states-max=i",
	"trans-max=i",
	"random-seed=i"
);

my $seed = $options{'random-seed'} || int(rand(2**31));

# $maxStates = 8;
# $maxTrans = 8

srand($seed);

my $machine;
my $stateId = 1;


sub createFindLCCABenchmark {
	my $where = shift;

	my $nestingDepth = 20;
	my $parallelStates = 20;

	$$where->{'name'} = 'findLCCA';
	$$where->{'type'} = 'scxml';
	$$where->{'intial'} = "";
	for (my $i = 1; $i <= $parallelStates; $i++) {
		$$where->{'initial'} .= "id" . ($i*$nestingDepth) . " ";
	}

	$$where->{'children'}[0]->{'type'} = 'parallel';
	$$where->{'children'}[0]->{'id'} = "p0";
	for (my $i = 0; $i < $parallelStates; $i++) {
		createFindLCCANestedCompounds(\$$where->{'children'}[0]->{'children'}, $nestingDepth, $nestingDepth * $parallelStates + 1);
	}

	$$where->{'children'}[1]->{'type'} = 'state';
	$$where->{'children'}[1]->{'id'} = "id".$stateId++;
	$$where->{'children'}[1]->{'transitions'}[0]->{'target'} = $$where->{'initial'};

}

sub createFindLCCANestedCompounds {
	my $where = shift;
	my $amount = shift;
	my $target = shift;

	if ($amount > 0) {
		my $state;
		$state->{'id'} = "id".$stateId++;
		$state->{'type'} = "state";
		createFindLCCANestedCompounds(\$state->{'children'}, $amount - 1, $target);
		
		if ($amount == 1) {
			$state->{'transitions'}[0]->{'target'} = "id".$target;
		}

		push @{$$where}, $state;
	}
}

sub createFinalParallelBenchmark {
	my $where = shift;

	my $nestingDepth = 20;
	my $finalStates = 20;

	$$where->{'name'} = 'finalParallel';
	$$where->{'type'} = 'scxml';
	$$where->{'intial'} = "";

	$$where->{'children'}[0]->{'type'} = 'parallel';
	$$where->{'children'}[0]->{'id'} = "p0";

	$$where->{'children'}[0]->{'transitions'}[0]->{'event'} = 'done.state.p0';
	$$where->{'children'}[0]->{'transitions'}[0]->{'target'} = 'p0';

	for (my $i = 0; $i < $finalStates; $i++) {
		createFinalParallelNestedFinals(\$$where->{'children'}[0]->{'children'}, $nestingDepth);
	}


}

sub createFinalParallelNestedFinals {
	my $where = shift;
	my $amount = shift;

	if ($amount > 0) {
		my $state;		
		if ($amount == 1) {
			$state->{'type'} = "final";
		} else {
			$state->{'type'} = "state";
		}
		$state->{'id'} = "id".$stateId++;
		
		createFinalParallelNestedFinals(\$state->{'children'}, $amount - 1);

		push @{$$where}, $state;
	}

}

sub writeState {
	my $state = shift;
	my $fh = shift;

	print $fh '<'.$state->{'type'};
	print $fh ' id="'.$state->{'id'} . '"' if $state->{'id'};
	print $fh ' type="deep"' if exists $state->{'deep'};
	print $fh '>';

	foreach (@{$state->{'children'}}) {
		writeState($_, $fh);
	}

	foreach (@{$state->{'transitions'}}) {
		writeTransition($_, $fh);
	}

	print $fh '</'.$state->{'type'} . '>';
	
};

sub writeTransition {
	my $trans = shift;
	my $fh = shift;

	print $fh '<transition';
	print $fh ' target="' . $trans->{'target'} . '"' if $trans->{'target'};
	print $fh ' event="' . $trans->{'event'} . '"' if $trans->{'event'};
	print $fh ' cond="' . $trans->{'cond'} . '"' if $trans->{'cond'};

	if ($trans->{'execContent'}) {
		print $fh '>';
		foreach (@{$trans->{'execContent'}}) {
			print $fh $_;
		}
		print $fh '</transition>';
	} else {
		print $fh '/>';
	}
	
};

sub writeMachine {
	my $machine = shift;
	my $file = shift;

	open(my $fh, ">", $file) or die "Can't open > $file: $!";

	print $fh '<scxml';
	print $fh ' datamodel="' . $machine->{'datamodel'} . '"' if $machine->{'datamodel'};
	print $fh ' seed="' . $seed . '"';
	print $fh ' name="' . $machine->{'name'} . '"' if $machine->{'name'};
	print $fh ' initial="' . $machine->{'initial'} . '"' if $machine->{'initial'};
	print $fh '>';
	
	foreach (@{$machine->{'children'}}) {
		writeState($_, $fh);
	}
	
	print $fh '</scxml>';
}

sub xmllint {
	my $file = shift;
	`mv $file $file.unformatted.xml`;
	`xmllint --format $file.unformatted.xml > $file`;
	`rm $file.unformatted.xml`;
}

{
	$machine = {};
	$stateId = 1;

	createFindLCCABenchmark(\$machine);
	# print Dumper($machine);
	writeMachine($machine, "findLCCA.scxml");
	xmllint("findLCCA.scxml");


	$machine = {};
	$stateId = 1;
	createFinalParallelBenchmark(\$machine);
	writeMachine($machine, "finalParallel.scxml");
	xmllint("finalParallel.scxml");

}
