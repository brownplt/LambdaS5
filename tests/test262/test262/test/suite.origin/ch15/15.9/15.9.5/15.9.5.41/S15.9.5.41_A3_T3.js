// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    The Date.prototype.setUTCFullYear property "length" has { ReadOnly,
    DontDelete, DontEnum } attributes
es5id: 15.9.5.41_A3_T3
description: Checking DontEnum attribute
---*/

if (Date.prototype.setUTCFullYear.propertyIsEnumerable('length')) {
  $ERROR('#1: The Date.prototype.setUTCFullYear.length property has the attribute DontEnum');
}

for(x in Date.prototype.setUTCFullYear) {
  if(x === "length") {
    $ERROR('#2: The Date.prototype.setUTCFullYear.length has the attribute DontEnum');
  }
}
// es5id: S15.9.5.41_A3_T3
