#!/bin/bash

PASSED=0
FAILED=0

source save_snapshots.sh

for file in `ls unit-tests/*.js`; do
  STR1=`../obj/s5.d.byte -load init.heap -desugar $file -print-string "optimize $file" -count-nodes -opt-const-propagation -count-nodes -print-string "end $file" -continue-s5-eval`
  TEST=`echo "$STR1" | grep "passed\|Passed"`

  if [ -n "$TEST" ]; then
    PASSED=$(($PASSED+1))
  else
    echo "FAILED"
    echo $file
    echo $STR1
    FAILED=$(($FAILED+1))
  fi
  echo "$STR1"
done

echo "$PASSED tests passed"
echo "$FAILED tests failed"
