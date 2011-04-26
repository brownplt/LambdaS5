function foo() {
    try {
        var a = arguments.caller;
    }
    catch(e) {
        print("Passed");
    }
}
foo();
