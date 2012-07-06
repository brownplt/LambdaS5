import os
import subprocess
import sys
import tempfile
import time
import re

timeout_seconds = 4

def nocomments(s):
  rx = re.compile("^//.*$", re.MULTILINE)
  return "".join(re.split(rx, s))

# Sophisticated Ph.D level error detection solution: string matching
# Patent Pending
parseerror   = "XXXParseErrorXXX"
passed       = "HARNESS: Passed"
failed       = "HARNESS: Failed"
jsonerr      = "Json_type.Json_error"
ocamlfailure = "Failure"

framework = open("test262/test/harness/framework.js").read()

def buildHarnessed(jsfile):
  testjs = jsfile.read()
  alljs = """
var currentTest;
var window = this;
function go() {
%s
%s
}
try {
  go();
} catch (e) {
  if (e instanceof Test262Error) {
    print('%s');
  } else {
    print('%s');
  }
}

print('%s');
print('done');
"""
  alljs = alljs % (framework, testjs, failed, ocamlfailure, passed)
  alljs = nocomments(alljs)
  return alljs


def parse(useC3, js):
  (jsfile, jsfilename) = tempfile.mkstemp()
  jsfilename = jsfilename.replace('\\', '\\\\')
  jsfile = os.fdopen(jsfile, 'w')
  parsejs = "print(JSON.stringify(Reflect.parse(read('%s'),{loc:true,source:'%s'}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))" % (jsfilename, jsfilename)
  jsfile.write(js)
  jsfile.flush()
  jsfile.close()

  if useC3:
    command = ["../../bin/jstest.exe", "-e", parsejs]
  else:
    command = ['../../bin/js', '-e', parsejs]


  runner = subprocess.Popen(command,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            cwd=".")

  (out, err) = runner.communicate()

  os.remove(jsfilename)

  def decode(someStr):
    try:
      return someStr.decode('utf-8')
    except UnicodeDecodeError:
      return "SyntaxError"

  err = decode(err)
  if err.find("SyntaxError") != -1 or err.find("ReferenceError") != -1:
    return (parseerror, err)

  out = decode(out)
  if useC3 and (out.find("Syntax error") != -1):
    return (parseerror, out)

  if out != "":
    return ("success", out)
  else:
    return (parseerror, "Nothing on stdout, error was: %s" % err)

def run(useC3, json):
  (outcome, json) = json
  if (outcome != "success"):
    return (outcome, "", json)
  (jsonfile, jsonfilename) = tempfile.mkstemp()
  jsonfile = os.fdopen(jsonfile, 'w')
  jsonfile.write(json)
  jsonfile.close()

  if useC3:
    command = ["ocamlrun", "../../obj/s5.d.byte",
               "-set-json", "./c3desugar.bat",
               "-c3-js", jsonfilename, "-js-to-s5",
               "-env", "../../envs/es5.env", "-apply",
               "-eval"]
  else:
    command = ["ocamlrun", "../../obj/s5.d.byte",
               "-set-json", "./desugar.sh",
               "-js", jsonfilename, "-js-to-s5",
               "-env", "../../envs/es5.env", "-apply",
               "-eval"]

  p = subprocess.Popen(command,
                       stdin=subprocess.PIPE,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE,
                       cwd=".")
  
  start = time.time()

  try:
    while(True):
      now = time.time()
      p.poll()
      if (p.returncode is None) and (now - start > timeout_seconds):
        p.kill()
        p.terminate()
        return ("Timeout", None, None)
      elif (not p.returncode is None):
        (out, err) = p.communicate()
        out = out.decode('utf-8')
        err = err.decode('utf-8')
        if (out.find(passed) != -1):
          return ("Success", out, err)
        elif (out.find(failed) != -1):
          return ("HarnessFailure", out, err)
        elif (out.find(jsonerr) != -1 or err.find(jsonerr) != -1):
          return ("JsonError", out, err)
        elif (out.find(ocamlfailure) != -1):
          return ("Exception", out, err)
        elif (err.find("WithError") != -1):
          return ("With", out, err)
        else:
          return ("OtherFailure", out, err)
  finally:
    os.remove(jsonfilename)

if __name__ == '__main__':
  if sys.argv[1] == "-c3":
    useC3 = True
    fileName = sys.argv[2]
  else:
    useC3 = False
    fileName = sys.argv[1]
  
  #print("Outcome: %s\nStdout:\n%s\nStderr:\n%s\n" % run(useC3, parse(useC3, buildHarnessed(open(fileName)))))
  print(run(useC3, parse(useC3, buildHarnessed(open(fileName)))))
