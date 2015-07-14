// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-6-a-13
description: >
    Object.defineProperties - 'O' is an Array object which implements
    its own [[GetOwnProperty]] method to get 'P' (8.12.9 step 1 )
includes:
    - runTestCase.js
    - dataPropertyAttributesAreCorrect.js
---*/

function testcase() {
        var arr = [];

        Object.defineProperty(arr, "prop", {
            value: 11,
            configurable: false
        });

        try {
            Object.defineProperties(arr, {
                prop: {
                    value: 12,
                    configurable: true
                }
            });
            return false;
        } catch (e) {
            return e instanceof TypeError && dataPropertyAttributesAreCorrect(arr, "prop", 11, false, false, false);
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.7-6-a-13
