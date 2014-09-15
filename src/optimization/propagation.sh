#!/bin/sh

./s5.d.byte -s5 t.s5 -opt-const-propagation -print-src
./s5.d.byte -s5 t.s5 -env ../envs/es5.env -apply -opt-const-propagation -print-src -eval
