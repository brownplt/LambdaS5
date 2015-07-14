// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.16-7-c-i-1
description: >
    Array.prototype.every - element to be retrieved is own data
    property on an Array-like object
includes: [runTestCase.js]
---*/

function testcase() {

        var kValue = { };
        function callbackfn(val, idx, obj) {
            if (idx === 5) {
                return val !== kValue;
            } else {
                return true;
            }
        }

        var obj = { 5: kValue, length: 100 };

        return !Array.prototype.every.call(obj, callbackfn);
    }
runTestCase(testcase);
// es5id: 15.4.4.16-7-c-i-1
