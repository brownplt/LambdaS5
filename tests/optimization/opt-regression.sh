#!/bin/sh

if [ -x $1 ]
then
    echo "$0 <opt-options>"
    exit 1
fi

PASSED=0
FAILED=0

DIR=`dirname $0`
cd $DIR/..

for file in `ls unit-tests/*.js`
do
    echo "$file"
    RUN=`ocamlrun ../obj/s5.d.byte \
      -desugar $file \
      -env ../envs/regexp.env -apply \
      -desugar ../lib/js-regexp/regexp.js -to-env -apply \
      -env ../envs/json.env -apply \
      -desugar ../lib/json/json_parse.js -to-env -apply \
      -desugar ../lib/json/json2.js -to-env -apply \
      -internal-env env-vars -apply \
      -env ../envs/es5.env -apply \
      -count-nodes "$file non-optimized" \
      $1 \
      -count-nodes "$file optimized" \
      -eval`

    STR1=`echo "$RUN" | grep "passed\|Passed"`

    if [ -n "$STR1" ]; then
      PASSED=$(($PASSED+1))
      echo "$RUN"
    else
      echo "$RUN"
      echo "FAILED"
      FAILED=$(($FAILED+1))
    fi

done

echo "$PASSED tests passed"
echo "$FAILED tests failed"
