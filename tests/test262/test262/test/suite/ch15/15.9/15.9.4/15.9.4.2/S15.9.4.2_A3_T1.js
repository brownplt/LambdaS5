// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    The Date.parse property "length" has { ReadOnly, DontDelete, DontEnum }
    attributes
es5id: 15.9.4.2_A3_T1
description: Checking ReadOnly attribute
---*/

x = Date.parse.length;
Date.parse.length = 1;
if (Date.parse.length !== x) {
  $ERROR('#1: The Date.parse.length has the attribute ReadOnly');
}
// es5id: S15.9.4.2_A3_T1
