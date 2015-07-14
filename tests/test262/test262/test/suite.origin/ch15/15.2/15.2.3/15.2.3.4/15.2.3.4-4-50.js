// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.4-4-50
description: >
    Object.getOwnPropertyNames - non-enumerable own property of 'O' is
    pushed into the returned Array
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};

        Object.defineProperty(obj, "nonEnumerableProp", {
            value: 10,
            enumerable: false,
            configurable: true
        });

        var result = Object.getOwnPropertyNames(obj);

        return result[0] === "nonEnumerableProp";
    }
runTestCase(testcase);
// es5id: 15.2.3.4-4-50
