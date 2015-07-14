// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Inside a CharacterClass, \b means the backspace character
es5id: 15.10.2.13_A3_T4
description: Execute /[^\[\b\]]+/.exec("abcdef") and check results
---*/

__executed = /[^\[\b\]]+/.exec("abcdef");

__expected = ["abcdef"];
__expected.index = 0;
__expected.input = "abcdef";

//CHECK#1
if (__executed.length !== __expected.length) {
	$ERROR('#1: __executed = /[^\\[\\b\\]]+/.exec("abcdef"); __executed.length === ' + __expected.length + '. Actual: ' + __executed.length);
}

//CHECK#2
if (__executed.index !== __expected.index) {
	$ERROR('#2: __executed = /[^\\[\\b\\]]+/.exec("abcdef"); __executed.index === ' + __expected.index + '. Actual: ' + __executed.index);
}

//CHECK#3
if (__executed.input !== __expected.input) {
	$ERROR('#3: __executed = /[^\\[\\b\\]]+/.exec("abcdef"); __executed.input === ' + __expected.input + '. Actual: ' + __executed.input);
}

//CHECK#4
for(var index=0; index<__expected.length; index++) {
	if (__executed[index] !== __expected[index]) {
		$ERROR('#4: __executed = /[^\\[\\b\\]]+/.exec("abcdef"); __executed[' + index + '] === ' + __expected[index] + '. Actual: ' + __executed[index]);
	}
}
// es5id: S15.10.2.13_A3_T4
