#!/usr/bin/bash
#RUN AS: $ for i in 1024 2048 3000 4096 6000 8192 12000 16300 16384 18000; do echo $i; bash runAll.sh $i; done

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
#POST PROCESS

#cat results.out | sed 's/\// /g;s/\. //g;s/_/ /g;s/\.exe//g' | awk '{$1=""; if ($3=="AUTO"){$3=$2; $2="AUTO";} if ($4=="NO" && $5 == "CO"){$4="NO-CO"; $5=""} for(i=1;i<=NF;i++) {if ($i != "") {printf $i"\t";}} print ""}' | sed 's/ /\t/g' > results1119_1145am.tsv

