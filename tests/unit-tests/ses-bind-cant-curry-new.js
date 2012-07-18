function test_BIND_CANT_CURRY_NEW() {
  function construct(f, args) {
    var bound = Function.prototype.bind.apply(f, [null].concat(args));
    return new bound();
  }
  var d;
    d = construct(Date, [1957, 4, 27]);
/*  try {
    d = construct(Date, [1957, 4, 27]);
  } catch (err) {
    if (err instanceof TypeError) { return true; }
    return 'Curries construction failed with: ' + err;
  }*/
  return d;
/*  if (typeof d === 'string') { return true; } // Opera
  var str = objToString.call(d);
  if (str === '[object Date]') { return false; }
  return 'Unexpected ' + str + ': ' + d;*/
}

test_BIND_CANT_CURRY_NEW();
