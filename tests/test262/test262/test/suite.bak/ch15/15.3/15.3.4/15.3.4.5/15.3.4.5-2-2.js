// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
info: >
    15.3.4.5 step 2 specifies that a TypeError must be thrown if the Target
    is not callable.
es5id: 15.3.4.5-2-2
description: >
    Function.prototype.bind throws TypeError if the Target is not
    callable (bind attached to object)
includes: [runTestCase.js]
---*/

function testcase() {
  // dummy function 
  function foo() {}
  var f = new foo();
  f.bind = Function.prototype.bind;

  try {
    f.bind();
  }
  catch (e) {
    if (e instanceof TypeError) {
      return true;
    }
  }
 }
runTestCase(testcase);
// es5id: 15.3.4.5-2-2
