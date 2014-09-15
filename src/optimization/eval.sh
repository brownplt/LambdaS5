#!/bin/sh

../s5.d.byte -desugar t.js -print-src -env ../../envs/es5.env -apply -eval
