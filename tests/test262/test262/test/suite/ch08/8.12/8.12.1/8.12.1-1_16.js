// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 8.12.1-1_16
description: >
    Properties - [[HasOwnProperty]] (non-writable, configurable,
    enumerable inherited value property)
includes: [runTestCase.js]
---*/

function testcase() {

    var base = {};
    Object.defineProperty(base, "foo", {value: 42, configurable:true, enumerable:true});
    var o = Object.create(base);
    return o.hasOwnProperty("foo")===false;

}
runTestCase(testcase);
// es5id: 8.12.1-1_16
