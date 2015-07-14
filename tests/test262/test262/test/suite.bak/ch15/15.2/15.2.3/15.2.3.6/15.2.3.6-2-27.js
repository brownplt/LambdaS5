// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-2-27
description: >
    Object.defineProperty - argument 'P' is a decimal that converts to
    a string (value is 123.456)
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};
        Object.defineProperty(obj, 123.456, {});

        return obj.hasOwnProperty("123.456");

    }
runTestCase(testcase);
// es5id: 15.2.3.6-2-27
