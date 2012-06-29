try {
  eval("x");
}
catch (e) {
  if (e instanceof ReferenceError) {
    console.log('Passed');
  }
}
