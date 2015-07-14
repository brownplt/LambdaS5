// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    RegExp.prototype.exec(string) Performs a regular expression match of ToString(string) against the regular expression and
    returns an Array object containing the results of the match, or null if the string did not match
es5id: 15.10.6.2_A1_T8
description: >
    String is {toString:void 0, valueOf:function(){throw "invalof";}}
    and RegExp is /[a-z]/
---*/

//CHECK#1
try {
  $ERROR('#1.1: /[a-z]/.exec({toString:void 0, valueOf:function(){throw "invalof"}}) throw "invalof". Actual: ' + (/[a-z]/.exec({toString:void 0, valueOf:function(){throw "invalof"}})));
} catch (e) {
  if (e !== "invalof") {
    $ERROR('#1.2: /[a-z]/.exec({toString:void 0, valueOf:function(){throw "invalof"}}) throw "invalof". Actual: ' + (e));
  }
}
// es5id: S15.10.6.2_A1_T8
