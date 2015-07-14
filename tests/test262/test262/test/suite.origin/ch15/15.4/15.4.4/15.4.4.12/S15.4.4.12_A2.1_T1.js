// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Operator use ToInteger from start
es5id: 15.4.4.12_A2.1_T1
description: start is not integer
---*/

var x = [0,1,2,3];
var arr = x.splice(1.5,3);

//CHECK#1
arr.getClass = Object.prototype.toString;
if (arr.getClass() !== "[object " + "Array" + "]") {
  $ERROR('#1: var x = [0,1,2,3]; var arr = x.splice(1.5,3); arr is Array object. Actual: ' + (arr.getClass()));
}

//CHECK#2
if (arr.length !== 3) {
  $ERROR('#2: var x = [0,1,2,3]; var arr = x.splice(1.5,3); arr.length === 3. Actual: ' + (arr.length));
}      

//CHECK#3
if (arr[0] !== 1) {
  $ERROR('#3: var x = [0,1,2,3]; var arr = x.splice(1.5,3); arr[0] === 1. Actual: ' + (arr[0]));
}

//CHECK#4
if (arr[1] !== 2) {
  $ERROR('#4: var x = [0,1,2,3]; var arr = x.splice(1.5,3); arr[1] === 2. Actual: ' + (arr[1]));
}      

//CHECK#5
if (arr[2] !== 3) {
  $ERROR('#5: var x = [0,1,2,3]; var arr = x.splice(1.5,3); arr[2] === 3. Actual: ' + (arr[2]));
}   

//CHECK#6
if (x.length !== 1) {
  $ERROR('#6: var x = [0,1,2,3]; var arr = x.splice(1.5,3); x.length === 1. Actual: ' + (x.length));
} 

//CHECK#7
if (x[0] !== 0) {
  $ERROR('#7: var x = [0,1,2,3]; var arr = x.splice(1.5,3); x[0] === 0. Actual: ' + (x[0]));
}
// es5id: S15.4.4.12_A2.1_T1
