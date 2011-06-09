#!/bin/bash

for file in `ls unit-tests/*.js`; do
  echo $file
  STR1=`./silent.sh $file | grep "passed"`
  echo $STR1

  echo ""
done
