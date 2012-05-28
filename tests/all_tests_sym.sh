#!/bin/bash

PASSED=0
FAILED=0

for file in `ls unit-tests/*.js`; do
  STR1=`./silent_sym.sh $file | grep "passed"`

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

