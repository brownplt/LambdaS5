// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: <LF> between chunks of one string not allowed
es5id: 8.4_A7.1
description: Insert <LF> between chunks of one string
negative: ReferenceError
---*/

eval("var x = asdf\u000Aghjk");
// es5id: S8.4_A7.1
