#!/bin/sh

PASSED=0
FAILED=0

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
      -print-string "optimize $file" \
      -count-nodes \
      -opt-const-propagation \
      -count-nodes \
      -print-string "end $file" \
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
