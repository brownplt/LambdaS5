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

ES5Harness = {};
ES5Harness.registerTest = function(test) {
    var error;
    if(test.precondition && !test.precondition()) {
        testRun(test.id, test.path, test.description, test.test.toString(),typeof test.precondition !== 'undefined' ? test.precondition.toString() : '', 'fail', 'Precondition Failed');
    } else {
        var testThis = test.strict===undefined ? window : undefined;
        try { var res = test.test.call(testThis); } catch(e) { res = 'fail'; error = e; }
        var retVal = /^s/i.test(test.id) ? (res === true || typeof res === 'undefined' ? 'pass' : 'fail') : (res === true ? 'pass' : 'fail');
        testRun(test.id, test.path, test.description, test.test.toString(), typeof test.precondition !== 'undefined' ? test.precondition.toString() : '', retVal, error);
    }
};
