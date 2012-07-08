var x = 1;

if (this.x !== 1) {
  throw("#1: variable x is a property of global object");
}

if(delete this.x !== false){
  throw("#2: variable x has property attribute DontDelete");
}

if(x === 1) {
  console.log('passed');
}

