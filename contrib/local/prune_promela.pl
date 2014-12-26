#!/usr/bin/perl -w

die("Not practical as spin reports superfluous line numbers after preprocessing - minimize SCXML instead");

use strict;
use File::Spec;
use File::Basename;

my $pmlIn = shift or die("Expected *.pml file as input");

# absolutize and split into components
$pmlIn = File::Spec->rel2abs($pmlIn) or die($!);
my($filename, $dirs, $suffix) = fileparse($pmlIn) or die($!);

my $spinOut = `spin -a $pmlIn`;
my $gccOut = `gcc -DMEMLIM=1024 -O2 -DVECTORSZ=2048 -DXUSAFE -w -o pan pan.c`;
my $panOut = `./pan -m10000 -a`;

my %unvisited;

for (split /^/, $panOut) {
	# /Users/sradomski/Desktop/foo.pml:128, state 12, "foreachIndex1 = 0"
	if (/$pmlIn:(\d+), state (\d+), "(.*)"/) {
		$unvisited{$1} = $3;
	}
}

open(my $fh, "<", $pmlIn) or die($!);
my $line = 0;
while(<$fh>) {
	if (exists($unvisited{$line}) && m/$unvisited{$line}/ ) {
		print "/* removed as unvisited */\n";
	} elsif (exists($unvisited{$line})) {
		chomp($_);
		chomp($unvisited{$line});
		print STDERR "$_ vs $unvisited{$line} \n";
	} else {		
		print;
	}
	$line++;
}
close($fh);