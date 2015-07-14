// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The Date.prototype has the property "getUTCHours"
es5id: 15.9.5_A19_T1
description: The Date.prototype has the property "getUTCHours"
---*/

if(Date.prototype.hasOwnProperty("getUTCHours") !== true){
  $ERROR('#1: The Date.prototype has the property "getUTCHours"');
}
// es5id: S15.9.5_A19_T1
