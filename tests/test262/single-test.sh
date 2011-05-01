#!/bin/bash

JSFILE=`mktemp`
NOCOMMENTS=`mktemp`
cat test262/test/harness/sta.js >> $JSFILE
cat S5_harness_before.js >> $JSFILE
cat $1 >> $JSFILE
cat $JSFILE


grep -Ev $'\r' $JSFILE | grep -Ev '\/\/*' > $NOCOMMENTS

cat $NOCOMMENTS > nocomments.txt

#for some reason 

JSONFILE=`mktemp`
../../bin/js -e "print(JSON.stringify(Reflect.parse(read('$NOCOMMENTS'),{loc:true}),{},2))" > $JSONFILE
echo "done parsing"
cat $JSONFILE > out2.txt
ocamlrun ../../src/s5.d.byte -desugar $JSONFILE -env ../../envs/es5.env -print es5
