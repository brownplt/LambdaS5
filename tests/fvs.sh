#!/bin/bash
if [ $# -eq 1 ]; then
   ../bin/js ../tests/json_print.js $1 >> $1.ast
   ocamlrun ../obj/s5.d.byte -js $1.ast -print-fvs
   rm $1.ast
else
   echo "usage: fvs.sh <filepath>"
fi
