if (arguments.length != 1) {
  print("usage: js json_print.js <filename>");
} else {
  var file = read(arguments[0]);
  var result = Reflect.parse(file, {loc : true, source: arguments[0]});
  print(JSON.stringify(
    result,
    function(key,value) {
      if(key==='value' && value instanceof RegExp) {
        return { re_lit: String(value) };
      }
      return value;
    },
    2));
}
