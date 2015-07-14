// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.19-1-10
description: Array.prototype.map - applied to the Math object
includes: [runTestCase.js]
---*/

function testcase() {
        function callbackfn(val, idx, obj) {
            return ('[object Math]' === Object.prototype.toString.call(obj));
        }
       
        try {
            Math.length = 1;
            Math[0] = 1;
            var testResult = Array.prototype.map.call(Math, callbackfn);
            return testResult[0] === true;
        } finally {
            delete Math[0];
            delete Math.length;
        }
    }
runTestCase(testcase);
// es5id: 15.4.4.19-1-10
