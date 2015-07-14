// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The String.prototype.concat.length property has the attribute DontDelete
es5id: 15.5.4.6_A9
description: >
    Checking if deleting the String.prototype.concat.length property
    fails
includes: [$FAIL.js]
---*/

//////////////////////////////////////////////////////////////////////////////
//CHECK#0
if (!(String.prototype.concat.hasOwnProperty('length'))) {
  $FAIL('#0: String.prototype.concat.hasOwnProperty(\'length\') return true. Actual: '+String.prototype.concat.hasOwnProperty('length')); 
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (delete String.prototype.concat.length) {
  $ERROR('#1: delete String.prototype.concat.length return false');
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#2
if (!(String.prototype.concat.hasOwnProperty('length'))) {
  $FAIL('#2: delete String.prototype.concat.length; String.prototype.concat.hasOwnProperty(\'length\') return true. Actual: '+String.prototype.concat.hasOwnProperty('length')); 
}
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S15.5.4.6_A9
