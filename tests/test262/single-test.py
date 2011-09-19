import os
import subprocess
import sys
import tempfile
import time
import re

def nocomments(s):
  rx = re.compile("^//.*$", re.MULTILINE)
  return "".join(re.split(rx, s))

harness = open("test262/test/harness/sta.js").read()
extra = open("S5_harness_before.js").read()
sputnik = open("test262/test/harness/sputnikLib.js").read()


def buildHarnessed(jsfile):
  testjs = jsfile.read()
  alljs = """
var currentTest;
var window = this;
%s
%s
%s
%s
print('done');
"""
  alljs = alljs % (harness, extra, sputnik, testjs)
  alljs = nocomments(alljs)
  return alljs


def parse(js):
  (jsfile, jsfilename) = tempfile.mkstemp()
  (parsefile, parsefilename) = tempfile.mkstemp()
  jsfile = os.fdopen(jsfile, 'w')
  parsefile = os.fdopen(parsefile, 'w')
  parsejs = "print(JSON.stringify(Reflect.parse(read('%s'),{loc:true}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))" % jsfilename
  jsfile.write(js)
  parsefile.write(parsejs)
  jsfile.flush()
  jsfile.close()

  runner = subprocess.Popen(["../../bin/js-1.8.5-Linux-i686", "-e", parsejs],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            cwd=".")

  (out, err) = runner.communicate()

  if err.find("SyntaxError") != -1:
    return 'ParseError'

  if out != "":
    return out
  else:
    raise Exception("Nothing on standard out from parse, stderr: %s" % err)

def run(json):
  (jsonfile, jsonfilename) = tempfile.mkstemp()
  jsonfile = os.fdopen(jsonfile, 'w')
  jsonfile.write(json)
  jsonfile.close()

  runner = subprocess.Popen(["ocamlrun", "../../obj/s5.d.byte",
                             "-desugar", jsonfilename,
                             "-env", "../../envs/es5.env",
                             "-json", "./desugar.sh",
                             "-eval"],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            cwd=".")

  (stdout, stderr) = runner.communicate()
  return (stdout, stderr)

if __name__ == '__main__':
  print(run(parse(buildHarnessed(open(sys.argv[1]))))[0])
