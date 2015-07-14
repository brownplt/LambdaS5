// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The undefined is DontEnum
es5id: 15.1.1.3_A3.2
description: Use for-in statement
---*/

// CHECK#1
for (prop in this) {
  if (prop === "undefined") {
	$ERROR('#1: The undefined is DontEnum');
  }	 	
}
// es5id: S15.1.1.3_A3.2
