#!/bin/bash

JSFILE=`mktemp`
NOCOMMENTS=`mktemp`
cat test262/test/harness/sta.js >> $JSFILE
cat S5_harness_before.js >> $JSFILE
cat $1 >> $JSFILE
echo "print('done');" >> $JSFILE

grep -Ev '//' $JSFILE > $NOCOMMENTS

cat $JSFILE > out1.txt

cat $NOCOMMENTS > out.txt


JSONFILE=`mktemp`
../../bin/js -e "print(JSON.stringify(Reflect.parse(read('$NOCOMMENTS'),{loc:true}),{},2))" > $JSONFILE

cat $JSONFILE > out2.txt

ocamlrun ../../src/s5.d.byte -desugar $JSONFILE -env ../../envs/es5.env -eval
