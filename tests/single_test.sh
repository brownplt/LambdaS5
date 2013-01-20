#!/bin/bash

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
      COMM='../obj/s5.d.byte -load init.heap -desugar '$2' -continue-'$TYPE'-eval'
      STR1=`$COMM`
      TEST=`echo $STR1 | grep "passed\|Passed"`
      if [ -n "$TEST" ]; then
        echo 'Passed'
      else
        echo 'Failed'
      fi
      if [ $VERB ]; then
        echo 'Test output:'
        echo $STR1
      fi
      exit 0
  fi
fi
echo "Usage: single_test.sh {s5, cesk} some/file/path.js (-v)"
exit 1
