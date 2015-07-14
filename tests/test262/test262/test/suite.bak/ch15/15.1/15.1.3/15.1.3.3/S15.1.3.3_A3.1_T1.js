// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    unescapedURISet containing one instance of each character valid in
    uriReserved
es5id: 15.1.3.3_A3.1_T1
description: Complex tests
---*/

uriReserved = [";", "/", "?", ":", "@", "&", "=", "+", "$", ","];
for (indexC = 0; indexC < uriReserved.length; indexC++) {
  var str = uriReserved[indexC];    
  if (encodeURI(str) !== str) {
    $ERROR('#' + (indexC + 1) + ': unescapedURISet containing' + str);
  }  
}
// es5id: S15.1.3.3_A3.1_T1
