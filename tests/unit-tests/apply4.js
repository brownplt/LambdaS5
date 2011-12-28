function g() {
  // gets called, but arguments empty
  if(arguments[0] === undefined && this === undefined) {
    print('passed');
  }
}

g.apply();
