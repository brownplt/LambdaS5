var x = 5;
function g(x) {
  eval("x = 22;")
  return x === 17;
}
if (g(17) && window.x === 22) {
  console.log("Passed");
}