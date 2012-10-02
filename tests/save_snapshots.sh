#!/bin/bash

# Take two snapshots: one right after s5 initialization, and one right after
# ses initialization. Save them in init.heap and ses.heap.
# Regenerate the snapshots if (i) they don't exist, or (ii) they are out of date

if [ ! -f init.heap    -o ../obj/s5.d.byte -nt init.heap \
  -o ! -f ses.heap     -o ../obj/s5.d.byte -nt ses.heap \
  -o ! -f seseval.heap -o ../obj/s5.d.byte -nt seseval.heap ]; then

echo "save_snapshots.sh: Rebuilding heap snapshots"

echo "___takeS5Snapshot()" | ./s5 stdin -eval-s5 -save init.heap

(cat ses/es-lab-tests/initSESPlus.js; echo "___takeS5Snapshot();") | ./s5 stdin -eval-s5 -save ses.heap

(cat ses/es-lab-tests/initSESPlus.js; echo "cajaVM.eval(\"___takeS5Snapshot();\");") | ./s5 stdin -eval-s5 -save seseval.heap

fi