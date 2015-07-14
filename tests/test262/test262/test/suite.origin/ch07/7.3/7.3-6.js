// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 7.3-6
description: >
    7.3 - ES5 recognizes the character <PS> (\u2029) as terminating
    string literal
includes: [runTestCase.js]
---*/

function testcase() {
        var prop = "66\u2029123";
        return prop === "66\u2029123" && prop[2] === "\u2029" && prop.length === 6;
    }
runTestCase(testcase);
// es5id: 7.3-6
