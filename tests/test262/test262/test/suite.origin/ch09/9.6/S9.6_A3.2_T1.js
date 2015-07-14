// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Operator uses floor, abs
es5id: 9.6_A3.2_T1
description: Use operator >>>0
---*/

// CHECK#1
if ((1.2345 >>> 0) !== 1) {
  $ERROR('#1: (1.2345 >>> 0) === 1. Actual: ' + ((1.2345 >>> 0)));
}

// CHECK#2
if ((-5.4321 >>> 0) !== 4294967291) {
  $ERROR('#2: (-5.4321 >>> 0) === 4294967291. Actual: ' + ((-5.4321 >>> 0)));
}
// es5id: S9.6_A3.2_T1
