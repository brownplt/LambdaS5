// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    Returns a boolean value (not a Boolean object) computed by
    ToBoolean(value)
es5id: 15.6.1.1_A1_T1
description: >
    Used values 1, new String("1"), new Object(1) and called without
    argument
---*/

//CHECK#1
if( typeof Boolean() !== "boolean" ) {
  $ERROR('#1: typeof Boolean() should be "boolean", actual is "'+typeof Boolean()+'"');
}

//CHECK#2
if( typeof Boolean(1) !== "boolean" ) {
  $ERROR('#2: typeof Boolean(1) should be "boolean", actual is "'+typeof Boolean(1)+'"');
}

//CHECK#3
if( typeof Boolean(new String("1")) !== "boolean" ) {
  $ERROR('#3: typeof Boolean(new String("1")) should be "boolean", actual is "'+typeof Boolean(new String("1"))+'"');
}

//CHECK#4
if( typeof Boolean(new Object(1)) !== "boolean" ) {
  $ERROR('#4: typeof Boolean(new Object(1)) should be "boolean", actual is "'+typeof Boolean(new Object(1))+'"');
}
// es5id: S15.6.1.1_A1_T1
