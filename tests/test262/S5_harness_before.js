/* Called from the child window after the test has run. */
function testRun(id, path, description, codeString, preconditionString, result, error) {
        currentTest = {id : id};
        currentTest.id = id;
        currentTest.path = path;
        currentTest.description = description;
        currentTest.result = result;
        currentTest.error = error;
        currentTest.code = codeString;
        currentTest.pre = preconditionString;
        if(result === 'pass') {
            print("HARNESS: Passed");
        }
        else {
            print("HARNESS: Failed");
        }
    }

print("333");
var ES5Harness = {};
print("444");
ES5Harness.registerTest = function(test) {
    var error;
    print("11");
    if(test.strict === 1) {
      print("STRICT TEST");
    }
    print("22");
    if(test.precondition && !test.precondition()) {
        testRun(test.id, test.path, test.description, test.test.toString(),typeof test.precondition !== 'undefined' ? test.precondition.toString() : '', 'fail', 'Precondition Failed');
    } else {
	print("1");
        var testThis = test.strict===undefined ? window : undefined;
	print("2");
        try { var res = test.test.call(testThis); } catch(e) { res = 'fail'; error = e; }
	print("3");

        // We skip this because we don't want to do Regex yet.  COME BACK TO IT!
        //        var retVal = /^s/i.test(test.id) ? (res === true || typeof res === 'undefined' ? 'pass' : 'fail') : (res === true ? 'pass' : 'fail');
        var retVal = (res === true || typeof res === 'undefined' ? 'pass' : 'fail');
        print("We think " + test.id + " did this: " + retVal +", because res was: " + (String(res)) + ", which was of type " + typeof res + ".  Error was: " + error);

        testRun(test.id, test.path, test.description, test.test.toString(), typeof test.precondition !== 'undefined' ? test.precondition.toString() : '', retVal, error);
    }
};
