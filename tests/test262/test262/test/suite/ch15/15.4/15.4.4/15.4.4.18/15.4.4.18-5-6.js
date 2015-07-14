// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.18-5-6
description: Array.prototype.forEach - thisArg is function
includes: [runTestCase.js]
---*/

function testcase() {
  var res = false;
  var result;
  function callbackfn(val, idx, obj)
  {
    result = this.res;
  }

  function foo(){}
  foo.res = true;
  
  var arr = [1];
  arr.forEach(callbackfn,foo)
  if( result === true)
    return true;    

 }
runTestCase(testcase);
// es5id: 15.4.4.18-5-6
