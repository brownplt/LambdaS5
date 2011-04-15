var program = "";
var line = null;
while ((line = readline()) !== null) {
  program = program.concat(line);
}

print(JSON.stringify(Reflect.parse(program)));