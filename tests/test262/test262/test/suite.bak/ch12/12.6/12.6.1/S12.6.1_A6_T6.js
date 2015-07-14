// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Expression in "do-while" IterationStatement is bracketed with braces
es5id: 12.6.1_A6_T6
description: Checking if execution of "do{}while 'hood'" fails
negative: SyntaxError
---*/

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
do break; while 'hood';
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S12.6.1_A6_T6
