#!/bin/bash

JSFILE=`mktemp js.XXXXXXXX`
NOCOMMENTS=`mktemp stripped.XXXXXXX`
echo "var currentTest;" >> $JSFILE
echo "var window = this;" >> $JSFILE

cat test262/test/harness/sta.js >> $JSFILE
cat S5_harness_before.js >> $JSFILE
cat test262/test/harness/sputnikLib.js >> $JSFILE
cat $1 >> $JSFILE
echo "print('done');" >> $JSFILE

grep -Ev '//' $JSFILE > $NOCOMMENTS

cat $JSFILE > out1.txt

cat $NOCOMMENTS > out.txt


JSONFILE=`mktemp json.XXXXXXX`
../../bin/js -e "print(JSON.stringify(Reflect.parse(read('$NOCOMMENTS'),{loc:true}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))" > $JSONFILE

cat $JSONFILE > out2.txt

RESULT=`mktemp result.XXXXXXXX`

ocamlrun ../../src/s5.d.byte -desugar $JSONFILE -env ../../envs/es5.env \
    -json ./desugar.sh -eval &> $RESULT

rm -f $JSONFILE
rm -f $NOCOMMENTS
rm -f $JSFILE

cat $RESULT

if grep -q "HARNESS: Passed" $RESULT; then
    rm -f $RESULT
    exit 0
fi

if grep -q "HARNESS: Failed" $RESULT; then
    rm -f $RESULT
    exit 4
fi

if grep -q "%%No eval yet%%" $RESULT; then
    rm -f $RESULT
    exit 3
fi

if grep -q "Json_type.Json_error" $RESULT; then
    rm -f $RESULT
    exit 2
fi

if grep -1 "with not allowed" $RESULT; then
  rm -f $RESULT
  exit 6
fi

if grep -1 "Failure" $RESULT; then
    rm -f $RESULT
    exit 1
fi

rm -f $RESULT
exit 5
