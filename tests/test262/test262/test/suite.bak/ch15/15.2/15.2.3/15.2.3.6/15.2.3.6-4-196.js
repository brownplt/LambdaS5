// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-4-196
description: >
    Object.defineProperty - 'O' is an Array, 'name' is an array index
    named property, 'name' is own accessor property that overrides an
    inherited data property (15.4.5.1 step 4.c)
includes: [runTestCase.js]
---*/

function testcase() {
        try {
            Object.defineProperty(Array.prototype, "0", {
                value: 11,
                configurable: true
            });

            var arrObj = [];
            Object.defineProperty(arrObj, "0", {
                get: function () { },
                configurable: false
            });

            Object.defineProperty(arrObj, "0", {
                configurable: true
            });
            return false;
        } catch (e) {
            return e instanceof TypeError;
        } finally {
            delete Array.prototype[0];
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.6-4-196
