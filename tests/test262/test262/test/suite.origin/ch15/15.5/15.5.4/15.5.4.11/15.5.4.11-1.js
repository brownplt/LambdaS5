// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.5.4.11-1
description: >
    'this' object used by the replaceValue function of a
    String.prototype.replace invocation
includes:
    - runTestCase.js
    - fnGlobalObject.js
---*/

function testcase() {
  var retVal = 'x'.replace(/x/, 
                           function() { 
                               if (this===fnGlobalObject()) {
                                   return 'y';
                               } else {
                                   return 'z';
                               }
                           });
  return retVal==='y';
}
runTestCase(testcase);
// es5id: 15.5.4.11-1
