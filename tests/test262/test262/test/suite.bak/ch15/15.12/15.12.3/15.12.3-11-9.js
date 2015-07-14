// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.12.3-11-9
description: JSON.stringify correctly works on top level Boolean objects.
includes: [runTestCase.js]
---*/

function testcase() {
  return JSON.stringify(new Boolean(false)) === 'false';
  }
runTestCase(testcase);
// es5id: 15.12.3-11-9
