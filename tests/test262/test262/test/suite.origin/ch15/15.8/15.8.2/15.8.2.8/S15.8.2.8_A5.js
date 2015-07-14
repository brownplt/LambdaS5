// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: If x is -Infinity, Math.exp(x) is +0
es5id: 15.8.2.8_A5
description: Checking if Math.exp(-Infinity) is +0
---*/

// CHECK#1
var x = -Infinity;
if (Math.exp(x) !== +0)
{
	$ERROR("#1: 'var x = -Infinity; Math.exp(x) !== +0'");
}
// es5id: S15.8.2.8_A5
