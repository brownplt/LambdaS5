#!/bin/bash
if [ $# -eq 1 ]; then
   ../bin/js ../tests/json_print.js $1 >> $1.ast
   ocamlrun ../src/s5.d.byte -desugar ../tests/$1.ast -print es5 -eval
   rm $1.ast
else
   echo "usage: unit_test.sh <filepath>"
fi
