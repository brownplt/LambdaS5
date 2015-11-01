#!/bin/bash

BASE_PATH=`dirname $0`/..

if [ ! -f 'init.heap' ]; then
  echo "Rebuilding heap snapshots..."
  source save_snapshots.sh &> /dev/null
fi

if [ $# -gt 1 ]; then
  TYPE=$1
  if [ $TYPE == 's5' -o $TYPE == 'cesk' ]; then
      VERB=''
      if [ "$#" -gt 2 -a "$3" == "-v" ]; then
        VERB='t'
        echo 'Running test file: '$2
      fi
      COMM=$BASE_PATH'/obj/s5.d.byte -load init.heap -desugar '$2' -continue-'$TYPE'-eval'
      STR1=`$COMM`
      TEST=`echo $STR1 | grep "passed\|Passed"`
      if [ -n "$TEST" ]; then
        echo 'Passed'
        RETURN_CODE=0
      else
        echo 'Failed'
        RETURN_CODE=1
      fi
      if [ $VERB ]; then
        echo 'Test output:'
        echo $STR1
      fi
      exit $RETURN_CODE
  fi
fi
echo "Usage: single_test.sh {s5, cesk} some/file/path.js (-v)"
exit 1
