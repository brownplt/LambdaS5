// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    The form (?= Disjunction ) specifies a zero-width positive lookahead.
    In order for it to succeed, the pattern inside Disjunction must match at the current position, but the current position is not advanced before matching the sequel.
    If Disjunction can match at the current position in several ways, only the first one is tried
es5id: 15.10.2.8_A1_T2
description: Execute /(?=(a+))a*b\1/.exec("baaabac") and check results
---*/

__executed = /(?=(a+))a*b\1/.exec("baaabac");

__expected = ["aba", "a"];
__expected.index = 3;
__expected.input = "baaabac";

//CHECK#1
if (__executed.length !== __expected.length) {
	$ERROR('#1: __executed = /(?=(a+))a*b\\1/.exec("baaabac"); __executed.length === ' + __expected.length + '. Actual: ' + __executed.length);
}

//CHECK#2
if (__executed.index !== __expected.index) {
	$ERROR('#2: __executed = /(?=(a+))a*b\\1/.exec("baaabac"); __executed.index === ' + __expected.index + '. Actual: ' + __executed.index);
}

//CHECK#3
if (__executed.input !== __expected.input) {
	$ERROR('#3: __executed = /(?=(a+))a*b\\1/.exec("baaabac"); __executed.input === ' + __expected.input + '. Actual: ' + __executed.input);
}

//CHECK#4
for(var index=0; index<__expected.length; index++) {
	if (__executed[index] !== __expected[index]) {
		$ERROR('#4: __executed = /(?=(a+))a*b\\1/.exec("baaabac"); __executed[' + index + '] === ' + __expected[index] + '. Actual: ' + __executed[index]);
	}
}
// es5id: S15.10.2.8_A1_T2
