#!/bin/bash

PASSED=0
FAILED=0

for file in `ls unit-tests/*.js`; do
  echo $file
  STR1=`./silent.sh $file | grep "passed"`
  echo $STR1

  if [ -n "$STR1" ]; then
    PASSED=$(($PASSED+1))
  else
    FAILED=$(($FAILED+1))
  fi

  echo ""
done

echo "$PASSED tests passed"
echo "$FAILED tests failed"

