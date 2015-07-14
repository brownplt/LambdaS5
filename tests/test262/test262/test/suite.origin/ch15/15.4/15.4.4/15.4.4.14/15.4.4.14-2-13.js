// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.14-2-13
description: >
    Array.prototype.indexOf - 'length' is inherited accessor property
    without a get function
includes: [runTestCase.js]
---*/

function testcase() {

        var proto = {};
        Object.defineProperty(proto, "length", {
            set: function () { },
            configurable: true
        });

        var Con = function () {};
        Con.prototype = proto;

        var child = new Con();
        child[1] = true;

        return Array.prototype.indexOf.call(child, true) === -1;
    }
runTestCase(testcase);
// es5id: 15.4.4.14-2-13
