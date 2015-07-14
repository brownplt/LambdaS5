// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: If x is +0, Math.asin(x) is +0
es5id: 15.8.2.3_A4
description: Checking if Math.asin(+0) equals +0
---*/

// CHECK#1
var x = +0;
if (Math.asin(x) !== +0)
{
	$ERROR("#1: 'var x = +0; Math.asin(x) !== +0'");
}
// es5id: S15.8.2.3_A4
