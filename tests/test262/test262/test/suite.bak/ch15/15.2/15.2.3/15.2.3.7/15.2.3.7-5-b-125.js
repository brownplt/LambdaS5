// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-5-b-125
description: >
    Object.defineProperties - 'descObj' is a Function object which
    implements its own [[Get]] method to get 'value' property (8.10.5
    step 5.a)
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};

        var func = function (a, b) {
            return a + b;
        };

        func.value = "Function";

        Object.defineProperties(obj, {
            property: func
        });

        return obj.property === "Function";
    }
runTestCase(testcase);
// es5id: 15.2.3.7-5-b-125
