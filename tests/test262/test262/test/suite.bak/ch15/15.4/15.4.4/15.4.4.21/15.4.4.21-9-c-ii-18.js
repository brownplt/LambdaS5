// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.21-9-c-ii-18
description: >
    Array.prototype.reduce - value of 'accumulator' used for first
    iteration is the value of 'initialValue' when it is present on an
    Array-like object
includes: [runTestCase.js]
---*/

function testcase() {

        var result = false;
        function callbackfn(prevVal, curVal, idx, obj) {
            if (idx === 0) {
                result = (arguments[0] === 1);
            }
        }

        var obj = { 0: 11, 1: 9, length: 2 };

        Array.prototype.reduce.call(obj, callbackfn, 1);
        return result;
    }
runTestCase(testcase);
// es5id: 15.4.4.21-9-c-ii-18
