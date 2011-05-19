function Bar() {

}
var o = {}
Bar.prototype = o;
function Foo() {

}

Foo.prototype = new Bar();

var o2 = new Bar();

if(o2 instanceof Foo) {
    print("passed");
}
