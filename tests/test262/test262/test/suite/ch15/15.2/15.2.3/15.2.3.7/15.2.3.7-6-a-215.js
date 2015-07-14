// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-6-a-215
description: >
    Object.defineProperties - 'O' is an Array, 'name' is an array
    index property, the [[Value]] field of 'desc' and the [[Value]]
    attribute value of 'name' are two numbers with same vaule
    (15.4.5.1 step 4.c)
includes:
    - runTestCase.js
    - dataPropertyAttributesAreCorrect.js
---*/

function testcase() {
        var arr = [];

        Object.defineProperty(arr, "0", {
            value: 101
        });

        try {
            Object.defineProperties(arr, {
                "0": {
                    value: 101
                }
            });
            return dataPropertyAttributesAreCorrect(arr, "0", 101, false, false, false);
        } catch (e) {
            return false;
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.7-6-a-215
