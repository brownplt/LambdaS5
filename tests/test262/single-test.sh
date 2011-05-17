#!/bin/bash

JSFILE=`mktemp -p /ltmp`
NOCOMMENTS=`mktemp -p /ltmp`
cat test262/test/harness/sta.js >> $JSFILE
cat S5_harness_before.js >> $JSFILE
cat $1 >> $JSFILE
echo "print('done');" >> $JSFILE

grep -Ev '//' $JSFILE > $NOCOMMENTS

cat $JSFILE > out1.txt

cat $NOCOMMENTS > out.txt


JSONFILE=`mktemp -p /ltmp`
../../bin/js -e "print(JSON.stringify(Reflect.parse(read('$NOCOMMENTS'),{loc:true}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))" > $JSONFILE

cat $JSONFILE > out2.txt

RESULT=`mktemp -p /ltmp`

ocamlrun ../../src/s5.d.byte -desugar $JSONFILE -env ../../envs/es5.env -eval &> $RESULT

cat $RESULT

if grep -q "HARNESS: Passed" $RESULT; then
    exit 0
fi

if grep -q "HARNESS: Failed" $RESULT; then
    exit 4
fi

if grep -q "%%No eval yet%%" $RESULT; then
    exit 3
fi

if grep -q "Json_type.Json_error" $RESULT; then
    exit 2
fi

if grep -1 "Failure" $RESULT; then
    exit 1
fi

exit 5
