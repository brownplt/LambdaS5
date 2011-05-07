#!/bin/bash

for file in `dir -d unit-tests/*.js`; do
  echo $file
  STR1=`./silent.sh $file | grep "passed"`
  echo $STR1

  echo ""
done
