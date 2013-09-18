#!/usr/bin/perl -w

use Math::Round;

my $pi = 3.14159;

# make one thousand requests with random parameters
for (my $i = 0; $i < 1000; $i++) {
  my $pitch = rand(2*$pi);
  my $roll = rand(2*$pi);
  my $yaw = rand(2*$pi);
  my $width = rand(400) + 200;
  my $height = rand(400) + 200;
  my $url = "http://epikur.local:8080/vrml/HARD_MP_VAL_002.png".
  "?pitch=".sprintf("%.3f",$pitch).
  "&roll=".sprintf("%.3f",$roll).
  "&yaw=".sprintf("%.3f",$yaw).
  "&width=".sprintf("%.0f",$width).
  "&height=".sprintf("%.0f",$height);
  print $url."\n";
  `wget '$url'`;  
}

# for (my $pitch = 0; $pitch < 2*$pi; $pitch += 0.01) {
#   for (my $roll = 0; $roll < 2*$pi; $roll += 0.01) {
#     for (my $yaw = 0; $yaw < 2*$pi; $yaw += 0.01) {
#       my $url = "http://epikur.local:8081/vrml/HARD_MP_VAL_002.png".
#       "?pitch=".sprintf("%.3f",$pitch).
#       "&roll=".sprintf("%.3f",$roll).
#       "&yaw=".sprintf("%.3f",$yaw);
#       print $url."\n";
#       `wget '$url'`;
#     }
#   }
# }