#!/usr/bin/perl -w

use strict;
use List::Util qw[min max sum];

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
my $maxDepth = $options{'depth-max'} || 6;
my $maxChilds = $options{'child-max'} || 6;
my $maxStates = $options{'states-max'} || 60;
my $maxTrans = $options{'trans-max'} || 6;
my $maxEvents = $options{'trans-max'} || int($maxStates / 3) + 1;

srand($seed);

my $machine;
my $stateId = 0;

my $probs = {
	'state' => {
		'type' => {
			'history' => 1,
			'parallel' => 2,
			'state' => 6,
			'final' => 1
		}
	},
	'transition' => {
		'target' => 0.8,
		'event' => 0.7,
		'cond' => 0.9,
		'execContent' => 0.7,
	},
	'history' => {
		'deep' => 0.2
	}
};

my $sumChildProbs = sum( values(%{$probs->{'state'}->{'type'}}));

sub putMachine {
	my $where = shift;
	
	$$where->{'name'} = 'test';
	$$where->{'type'} = 'scxml';
	$$where->{'datamodel'} = 'ecmascript';

	putState(\$$where->{'children'}, 0);
	putTransition(\$$where);
}

sub putTransition {
	my $where = shift;

	return if $$where->{'type'} eq 'final';

	my $nrTrans = int(rand($maxTrans + 1));
	$nrTrans = min($nrTrans, 1) if $$where->{'type'} eq 'history';

	for (my $i = 0; $i < $nrTrans; $i++) {

		my $trans;
		if (rand(1) < $probs->{'transition'}->{'target'}) {
			# has a target - pick one at random
			$trans->{'target'} = 'id' . int(rand($stateId));
		}

		if (rand(1) < $probs->{'transition'}->{'event'}) {
			# has an event
			$trans->{'event'} = 'e' . int(rand($maxEvents + 1));
		}

		if (rand(1) < $probs->{'transition'}->{'cond'}) {
			# has a condition
			if (int(rand(2)) > 0) {
				$trans->{'cond'} = 'true';
			} else {
				$trans->{'cond'} = 'false';
			}
		}

		if (rand(1) < $probs->{'transition'}->{'execContent'}) {
			# has a executable content
			push @{$trans->{'execContent'}}, '<log label="foo" />';
		}

		push @{$$where->{'transitions'}}, $trans;
	}

	# continue with childs
	foreach (@{$$where->{'children'}}) {
		putTransition(\$_);
	}
}

sub putState {
	my $where = shift;
	my $depth = shift;
	my $minStates = shift || 0;
	my $r;
	
	return if ($stateId > $maxStates);
	return if ($depth > $maxDepth);
	my $nrChilds = int(rand($maxChilds + 1));
	$nrChilds = max($minStates, $nrChilds);
	
	for (my $i = 0; $i < $nrChilds; $i++) {
		my $r = rand($sumChildProbs);
		
		my $state;
		foreach my $type (keys %{$probs->{'state'}->{'type'}}) {
			my $prob = $probs->{'state'}->{'type'}->{$type};
			if ($r < $prob) {
				$state->{'type'} = $type;
				last;
			}
			$r -= $prob;
		}
	
		$state->{'id'} = "id".$stateId++;
	
		if ($state->{'type'} eq 'parallel') {
			putState(\$state->{'children'}, $depth + 1, 2);
		} elsif ($state->{'type'} eq 'state') {
			putState(\$state->{'children'}, $depth + 1);
		} elsif ($state->{'type'} eq 'history') {
			if (rand(1) < $probs->{'history'}->{'deep'}) {
				$state->{'deep'} = 1;
			}
		}
	
		push @{$$where}, $state;
	}
};

sub writeState {
	my $state = shift;
	
	print STDOUT '<'.$state->{'type'};
	print STDOUT ' id="'.$state->{'id'} . '"';
	print STDOUT ' type="deep"' if exists $state->{'deep'};
	print STDOUT '>';

	foreach (@{$state->{'children'}}) {
		writeState($_);
	}

	foreach (@{$state->{'transitions'}}) {
		writeTransition($_);
	}

	print STDOUT '</'.$state->{'type'} . '>';
	
};

sub writeTransition {
	my $trans = shift;
	
	print STDOUT '<transition';
	print STDOUT ' target="' . $trans->{'target'} . '"' if $trans->{'target'};
	print STDOUT ' event="' . $trans->{'event'} . '"' if $trans->{'event'};
	print STDOUT ' cond="' . $trans->{'cond'} . '"' if $trans->{'cond'};

	if ($trans->{'execContent'}) {
		print STDOUT '>';
		foreach (@{$trans->{'execContent'}}) {
			print STDOUT $_;
		}
		print STDOUT '</transition>';
	} else {
		print STDOUT '/>';
	}
	
};

sub writeMachine {
	my $machine = shift;
	print STDOUT '<scxml';
	print STDOUT ' datamodel="' . $machine->{'datamodel'} . '"' if $machine->{'datamodel'};
	print STDOUT ' seed="' . $seed . '"';
	print STDOUT ' name="' . $machine->{'name'} . '"' if $machine->{'name'};
	print STDOUT '>';
	
	foreach (@{$machine->{'children'}}) {
		writeState($_);
	}
	
	print STDOUT '</scxml>';
}

putMachine(\$machine);
# print Dumper($machine);

writeMachine($machine);


#print Dumper($machine);


# writeState($machine);
