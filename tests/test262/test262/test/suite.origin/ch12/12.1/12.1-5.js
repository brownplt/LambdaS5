// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 12.1-5
description: "12.1 - block '{ StatementListopt };' is not allowed: if-else-if"
includes: [runTestCase.js]
---*/

function testcase() {
        try {
            eval("if{};else if{}");
            return false;
        } catch (e) {
            return e instanceof SyntaxError;
        }
    }
runTestCase(testcase);
// es5id: 12.1-5
