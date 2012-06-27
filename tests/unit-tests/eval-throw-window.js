try {
  eval("throw this;");
}
catch (e) {
  if (e === window) {
    console.log("Passed");
  }
}