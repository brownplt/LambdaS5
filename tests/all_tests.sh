#!/bin/bash

PASSED=0
FAILED=0

source save_snapshots.sh

for file in `ls unit-tests/*.js`; do
  STR1=`../obj/s5.d.byte -load init.heap -desugar $file -continue-s5-eval | grep "passed\|Passed"`

  if [ -n "$STR1" ]; then
    PASSED=$(($PASSED+1))
  else
    echo "FAILED"
    echo $file
    echo $STR1
    FAILED=$(($FAILED+1))
  fi
done

echo "$PASSED tests passed"
echo "$FAILED tests failed"

