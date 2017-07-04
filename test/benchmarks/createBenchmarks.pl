#!/usr/bin/perl -w

use strict;
use List::Util qw[min max sum];

use warnings;
no warnings 'recursion';

use Getopt::Long qw(GetOptions);
use Data::Dumper;

my $size = 20;
my %options = ();


my $machine;
my $stateId = 1;

### Find LCCA ===========

sub benchLCCA {
	my $where = shift;

	my $nestingDepth = $size;
	my $parallelStates = $size;

	$$where->{'name'} = 'benchmark';
	$$where->{'type'} = 'scxml';
	$$where->{'datamodel'} = 'null';
	$$where->{'initial'} = "mark";
	# SCION cannot have multiple states in its initial attribute
	# for (my $i = 1; $i <= $parallelStates; $i++) {
	# 	$$where->{'initial'} .= "id" . ($i*$nestingDepth) . " ";
	# }

	$$where->{'children'}[0]->{'type'} = 'parallel';
	$$where->{'children'}[0]->{'id'} = "mark";
	for (my $i = 0; $i < $parallelStates; $i++) {
		benchLCCANestedCompounds(\$$where->{'children'}[0]->{'children'}, $nestingDepth, $nestingDepth * $parallelStates + 1);
	}

	$$where->{'children'}[1]->{'type'} = 'state';
	$$where->{'children'}[1]->{'id'} = "id".$stateId++;
	$$where->{'children'}[1]->{'transitions'}[0]->{'target'} = "mark";

}

sub benchLCCANestedCompounds {
	my $where = shift;
	my $amount = shift;
	my $target = shift;

	if ($amount > 0) {
		my $state;
		$state->{'id'} = "id".$stateId++;
		$state->{'type'} = "state";
		benchLCCANestedCompounds(\$state->{'children'}, $amount - 1, $target);
		
		if ($amount == 1) {
			$state->{'transitions'}[0]->{'target'} = "id".$target;
		}

		push @{$$where}, $state;
	}
}

### Final Parallel States ===========

sub benchFinalParallel {
	my $where = shift;

	my $nestingDepth = $size;
	my $finalStates = $size;

	$$where->{'name'} = 'benchmark';
	$$where->{'type'} = 'scxml';
	$$where->{'datamodel'} = 'null';
	$$where->{'initial'} = "";

	$$where->{'children'}[0]->{'type'} = 'parallel';
	$$where->{'children'}[0]->{'id'} = "mark";

	$$where->{'children'}[0]->{'transitions'}[0]->{'event'} = 'done.state.mark';
	$$where->{'children'}[0]->{'transitions'}[0]->{'target'} = 'mark';

	for (my $i = 0; $i < $finalStates; $i++) {
		benchFinalParallelNested(\$$where->{'children'}[0]->{'children'}, $nestingDepth);
	}

}

sub benchFinalParallelNested {
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

		benchFinalParallelNested(\$state->{'children'}, $amount - 1);

		push @{$$where}, $state;
	}

}

### Conflicting Transitions ===========

sub benchConflictTrans {
	my $where = shift;

	my $nestingDepth = 1;
	my $transitions = $size;

	$$where->{'name'} = 'benchmark';
	$$where->{'type'} = 'scxml';
	$$where->{'datamodel'} = 'null';
	$$where->{'initial'} = "";

	$$where->{'children'}[0]->{'type'} = 'parallel';
	$$where->{'children'}[0]->{'id'} = "mark";
	for (my $i = 0; $i < $transitions; $i++) {
		benchConflictTransNested(\$$where->{'children'}[0]->{'children'}, $nestingDepth);
	}

	$$where->{'children'}[1]->{'type'} = 'state';
	$$where->{'children'}[1]->{'id'} = "id".$stateId++;
	$$where->{'children'}[1]->{'transitions'}[0]->{'target'} = "mark";

}

sub benchConflictTransNested {
	my $where = shift;
	my $amount = shift;

	if ($amount > 0) {
		my $state;
		$state->{'id'} = "id".$stateId++;
		$state->{'type'} = "state";
		benchConflictTransNested(\$state->{'children'}, $amount - 1);
		
		if ($amount == 1) {
			for (my $i = 0; $i < $size; $i++) {
				$state->{'transitions'}[$i]->{'target'} = "mark";
			}
		}

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
	print $fh ' name="' . $machine->{'name'} . '"' if $machine->{'name'};
	print $fh ' initial="' . $machine->{'initial'} . '"' if $machine->{'initial'};
	print $fh ' xmlns="http://www.w3.org/2005/07/scxml"';
	print $fh ' version="1.0"';
	print $fh '>';
	
	foreach (@{$machine->{'children'}}) {
		writeState($_, $fh);
	}
	
	print $fh '</scxml>';
}

sub xmllint {
	my $file = shift;
	# `mv $file $file.unformatted.xml`;
	# `xmllint --format $file.unformatted.xml > $file`;
	# `rm $file.unformatted.xml`;
}

{
	for my $i (4, 16, 64, 256, 512) {
		$size = $i;

		$machine = {};
		$stateId = 1;
		benchLCCA(\$machine);
		# print Dumper($machine);
		writeMachine($machine, "LCCA.${size}.scxml");
		xmllint("benchLCCA${size}.scxml");


		# $machine = {};
		# $stateId = 1;
		# benchFinalParallel(\$machine);
		# writeMachine($machine, "benchFinalParallel${size}.scxml");
		# xmllint("benchFinalParallel${size}.scxml");


		$machine = {};
		$stateId = 1;
		benchConflictTrans(\$machine);
		# print Dumper($machine);
		writeMachine($machine, "Transitions.${size}.scxml");
		xmllint("benchConflictTrans${size}.scxml");
	}
}
