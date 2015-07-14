// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The initial value of undefined is undefined
es5id: 15.1.1.3_A1
description: Use typeof, isNaN, isFinite
---*/

// CHECK#1
if (typeof(undefined) !== "undefined") {
	$ERROR('#1: typeof(undefined) === "undefined". Actual: ' + (typeof(undefined))); 
}

// CHECK#2
if (undefined !== void 0) {
	$ERROR('#2: undefined === void 0. Actual: ' + (undefined)); 
}

// CHECK#3
// es5id: S15.1.1.3_A1
