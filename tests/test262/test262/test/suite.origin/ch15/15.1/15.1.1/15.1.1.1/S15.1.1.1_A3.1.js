// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The NaN is DontDelete
es5id: 15.1.1.1_A3.1
description: Use delete
flags: [noStrict]
---*/

// CHECK#1
if (delete NaN !== false) {
	$ERROR('#1: delete NaN === false. Actual: ' + (delete NaN)); 	
}
// es5id: S15.1.1.1_A3.1
