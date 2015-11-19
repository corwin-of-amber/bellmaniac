#!/usr/bin/bash
if [ "$#" -ne 1 ]; then
    echo "Illegal number of parameters"
fi
N=$1
B=64
for e in `find ./Fixed -name *.exe`; do
    x=`$e $N $B`
    echo "$e $x" >>results.out
done    
for e in `find ./Auto -name *.exe`; do
    x=`$e $N $B`
    echo "$e $x" >>results.out 
done    
