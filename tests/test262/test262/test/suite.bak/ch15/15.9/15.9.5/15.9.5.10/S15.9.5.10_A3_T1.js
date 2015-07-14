// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    The Date.prototype.getFullYear property "length" has { ReadOnly,
    DontDelete, DontEnum } attributes
es5id: 15.9.5.10_A3_T1
description: Checking ReadOnly attribute
---*/

x = Date.prototype.getFullYear.length;
Date.prototype.getFullYear.length = 1;
if (Date.prototype.getFullYear.length !== x) {
  $ERROR('#1: The Date.prototype.getFullYear.length has the attribute ReadOnly');
}
// es5id: S15.9.5.10_A3_T1
