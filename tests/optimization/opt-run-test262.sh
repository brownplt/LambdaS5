#!/bin/sh

chs="ch07 ch08 ch09 ch10 ch11 ch12 ch13 ch14 ch15"
log=opt-run-test262.log
base=./opt-results
testscript=./opt-test-section.sh

rm -f $log
mkdir -p $base
for t in $chs
do
    echo "$t" >> $log
    $testscript $t > $base/$t-nonstrict.txt

    echo "strict $t" >> $log
    $testscript --strict $t > $base/$t-strict.txt
done
