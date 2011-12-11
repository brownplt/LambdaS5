function f() {
  if(arguments[0] === 22) {
    print('Passed');
  }
}

f.apply({}, [22]);
