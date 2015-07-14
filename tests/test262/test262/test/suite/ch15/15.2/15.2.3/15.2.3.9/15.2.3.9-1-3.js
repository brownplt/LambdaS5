// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.9-1-3
description: >
    Object.freeze throws TypeError if type of first param is boolean
    primitive
includes: [runTestCase.js]
---*/

function testcase() {
        var result = false;
        try {
            Object.freeze(false);

            return false;
        } catch (e) {
            result = e instanceof TypeError;
        }
        try {
            Object.freeze(true);

            return false;
        } catch (e) {
            return result && e instanceof TypeError;
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.9-1-3
