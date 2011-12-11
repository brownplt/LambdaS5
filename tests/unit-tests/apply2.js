function g() {
  if(arguments[1] === 'argument 2' && this.foo === 34) {
    print('Passed');
  }
}

g.apply({foo:34}, [,'argument 2']);
