#!/bin/bash
wl=300
seed=1
./runsolver --timestamp -d 15 -o output.out -v output.var -w output.wat -C $wl -W $wl ./nuwls-un $1 $seed 
cat output.out
rm -f output.out
rm -f output.var
rm -f output.wat
