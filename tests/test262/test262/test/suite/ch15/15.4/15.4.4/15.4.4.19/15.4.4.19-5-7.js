// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.19-5-7
description: Array.prototype.map - built-in functions can be used as thisArg
includes: [runTestCase.js]
---*/

function testcase() {

        function callbackfn(val, idx, obj) {
            return this === eval;
        }

        var testResult = [11].map(callbackfn, eval);
        return testResult[0] === true;
    }
runTestCase(testcase);
// es5id: 15.4.4.19-5-7
