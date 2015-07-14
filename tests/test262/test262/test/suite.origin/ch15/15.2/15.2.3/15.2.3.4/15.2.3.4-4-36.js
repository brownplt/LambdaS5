// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.4-4-36
description: >
    Object.getOwnPropertyNames - inherited data properties are not
    pushed into the returned array
includes: [runTestCase.js]
---*/

function testcase() {

        var proto = { "parent": "parent" };

        var Con = function () { };
        Con.prototype = proto;

        var child = new Con();

        var result = Object.getOwnPropertyNames(child);

        for (var p in result) {
            if (result[p] === "parent") {
                return false;
            }
        }
        return true;
    }
runTestCase(testcase);
// es5id: 15.2.3.4-4-36
