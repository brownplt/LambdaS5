function foo() {
    print("hi");
    print(this);
    for (var x in this) {
        print(x)
    }
}
foo()
