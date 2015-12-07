if (scriptArgs.length != 1) {
  print("usage: js json_print.js <filename>");
} else {
  var file = read(scriptArgs[0]);
  var result = Reflect.parse(file, {loc : true, source: scriptArgs[0]});
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
