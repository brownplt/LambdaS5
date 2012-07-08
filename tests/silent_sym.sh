#!/bin/bash
if [ $# -eq 1 ]; then
   ../bin/js ../tests/json_print.js $1 >> $1.ast
   ocamlrun ../obj/s5.d.byte -set-json ../src/desugar.sh \
           -js ../tests/$1.ast -js-to-s5 \
           -env ../envs/es5.env -apply \
           -sym-eval
   rm $1.ast
else
   echo "usage: silent_sym.sh <filepath>"
fi
