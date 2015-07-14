// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-3-206
description: >
    Object.defineProperty - 'get' property in 'Attributes' is not
    present (8.10.5 step 7)
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};

        Object.defineProperty(obj, "property", {
            set: function () {}
        });

        return typeof obj.property === "undefined" && obj.hasOwnProperty("property");
    }
runTestCase(testcase);
// es5id: 15.2.3.6-3-206
