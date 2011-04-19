if (arguments.length != 1) {
   print("usage: js json_print.js <filename>");
} else {
   var file = read(arguments[0]);
   var result = Reflect.parse(file, {loc : true});
   print(JSON.stringify(result, {}, 2));
}
