// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: If x is greater than 0 but less than 1, Math.floor(x) is +0
es5id: 15.8.2.9_A6
description: >
    Checking if Math.floor(x) is +0, where x is greater than 0 but
    less than 1
---*/

// CHECK#1
var x = 0.000000000000001;
if (Math.floor(x) !== +0)
{
	$ERROR("#1: 'var x = 0.000000000000001; Math.floor(x) !==  +0'");
}

// CHECK#2
var x = 0.999999999999999;
if (Math.floor(x) !== +0)
{
	$ERROR("#2: 'var x = 0.999999999999999; Math.ceil(x) !== +0'");
}

// CHECK#3
var x = 0.5;
if (Math.floor(x) !== +0)
{
	$ERROR("#3: 'var x = 0.5; Math.ceil(x) !== +0'");
}
// es5id: S15.8.2.9_A6
