var test1 = eval("'use strict';this") === window;
var test2 = eval("'use strict';this") === this;
if (test1 && test2) {
  console.log("Passed");
}
