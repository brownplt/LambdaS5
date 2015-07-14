// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.10.4.1-4
description: RegExp - the SyntaxError is not thrown when flags is 'gim'
includes: [runTestCase.js]
---*/

function testcase() {
        try {
            var regExpObj = new RegExp('abc', 'gim');

            return true;
        } catch (e) {
            return false;
        }
    }
runTestCase(testcase);
// es5id: 15.10.4.1-4
