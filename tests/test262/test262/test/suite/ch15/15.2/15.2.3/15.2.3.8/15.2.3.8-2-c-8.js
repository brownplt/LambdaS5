// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.8-2-c-8
description: Object.seal - 'O' is an Error object
includes: [runTestCase.js]
---*/

function testcase() {

        var errObj = new Error();
        var preCheck = Object.isExtensible(errObj);
        Object.seal(errObj);

        return preCheck && Object.isSealed(errObj);

    }
runTestCase(testcase);
// es5id: 15.2.3.8-2-c-8
