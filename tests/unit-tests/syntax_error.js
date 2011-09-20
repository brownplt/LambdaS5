var o = {
    test: function testcase() {
        "use strict";

        print('In test');

        try {
            eval("var _13_1_9_fun = function (param1, param2, param1) { };");
            return false;
        } catch (e) {
            return e instanceof SyntaxError;
        }
    },
};

if(o.test()) {
  print("Passed.");
}
else {
  print("Failed.");
}
