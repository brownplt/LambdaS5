// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-4-127
description: >
    Object.defineProperty - 'O' is an Array, 'name' is the length
    property of 'O', test the [[Value]] field of 'desc' is a boolean
    with value false (15.4.5.1 step 3.c)
includes: [runTestCase.js]
---*/

function testcase() {

        var arrObj = [0, 1];

        Object.defineProperty(arrObj, "length", {
            value: false
        });
        return arrObj.length === 0 && !arrObj.hasOwnProperty("0") && !arrObj.hasOwnProperty("1");

    }
runTestCase(testcase);
// es5id: 15.2.3.6-4-127
