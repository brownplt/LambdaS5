var test1 = eval("this") === window;
var test2 = eval("this") === this;
if (test1 && test2) {
  console.log("Passed");
}