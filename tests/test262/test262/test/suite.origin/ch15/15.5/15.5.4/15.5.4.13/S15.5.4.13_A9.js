// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The String.prototype.slice.length property has the attribute DontDelete
es5id: 15.5.4.13_A9
description: >
    Checking if deleting the String.prototype.slice.length property
    fails
includes: [$FAIL.js]
---*/

//////////////////////////////////////////////////////////////////////////////
//CHECK#0
if (!(String.prototype.slice.hasOwnProperty('length'))) {
  $FAIL('#0: String.prototype.slice.hasOwnProperty(\'length\') return true. Actual: '+String.prototype.slice.hasOwnProperty('length'));
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (delete String.prototype.slice.length) {
  $ERROR('#1: delete String.prototype.slice.length return false');
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#2
if (!(String.prototype.slice.hasOwnProperty('length'))) {
  $FAIL('#2: delete String.prototype.slice.length; String.prototype.slice.hasOwnProperty(\'length\') return true. Actual: '+String.prototype.slice.hasOwnProperty('length'));
}
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S15.5.4.13_A9
