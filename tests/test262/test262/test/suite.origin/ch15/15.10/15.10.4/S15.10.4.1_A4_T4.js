// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: let F be the empty string if flags is undefined
es5id: 15.10.4.1_A4_T4
description: RegExp is new RegExp(null,void 0)
---*/

__re = new RegExp(null, void 0);

//CHECK#1
if (__re.source !== "null") {
  $ERROR('#1: __re = new RegExp(null, void 0); __re.source === "null". Actual: '+ (__re.source));
}

//CHECK#2
if (__re.multiline !== false) {
  $ERROR('#2: __re = new RegExp(null, void 0); __re.multiline === false. Actual: ' + (__re.multiline));
}

//CHECK#3
if (__re.global !== false) {
  $ERROR('#3: __re = new RegExp(null, void 0); __re.global === false. Actual: ' + (__re.global));
}

//CHECK#4
if (__re.ignoreCase !== false) {
  $ERROR('#4: __re = new RegExp(null, void 0); __re.ignoreCase === false. Actual: ' + (__re.ignoreCase));
}
// es5id: S15.10.4.1_A4_T4
