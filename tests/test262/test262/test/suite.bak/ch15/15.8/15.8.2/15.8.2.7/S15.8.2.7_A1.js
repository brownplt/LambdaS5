// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: If x is NaN, Math.cos(x) is NaN
es5id: 15.8.2.7_A1
description: Checking if Math.cos(NaN) is NaN
---*/

// CHECK#1
var x = NaN;
if (!isNaN(Math.cos(x)))
{
	$ERROR("#1: 'var x=NaN; isNaN(Math.cos(x)) === false'");
}
// es5id: S15.8.2.7_A1
