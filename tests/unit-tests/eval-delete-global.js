window.x = 5;
try {
  eval("delete window.x; x;");
}
catch (e) {
  if (e instanceof ReferenceError) {
    console.log("Passed");
  }
}