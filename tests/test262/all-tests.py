import os
import subprocess
import time
import sys
from single_test import *

result_dir = "results-new"

def testFile(f):
  parsed = parse(buildHarnessed(open(f)))
  if parsed == "ParseError":
    return ("<li class='passed'><a href='%s'>%s</a></li>" % (str(f), str(f)), 1, 0)

  (typ, stdout, stderr) = run(parsed)

  if typ == "Timeout":
    return ("<li class='failed'><a href='%s'>%s</a> (Terminated)</li>" % (str(f), str(f)), 0, 1)
  elif typ == "Success":
    return ("<li class='passed'><a href='%s'>%s</a></li>" % (str(f), str(f)), 1, 0)
  else: # typ is "Failure"
    return ("<li class='failed'><div><a href='%s'>%s</a> (Failed)</div> \
              <div>Type:%s</div> \
              <div>Stdout:</div> \
              <p>%s</p> \
              <div>Stderr:</div> \
              <p>%s</p> \
            </li>" % (str(f), str(f), typ, stdout, stderr), 0, 1)

def testDir(d):
  files = os.listdir(str(d))
  inner = ""
  passed = 0
  failed = 0
  for f in files:
    f = os.path.join(str(d), f)
    if(os.path.isdir(f)):
      (fHtml, fPassed, fFailed) = testDir(f)
    else:
      (fHtml, fPassed, fFailed) = testFile(f)
    passed += fPassed
    failed += fFailed
    inner += fHtml

  color = 'failed'
  if failed == 0:
    color = 'passed'

  return ("<li class='%s'>%s; %s passed, %s failed \
          <a href='#' class='toggle'>(show/hide)</a> \
          <ul class='showing'>%s</ul></li>" % (color, str(d), passed, failed, inner),
          passed,
          failed)

template = """
<html>
<head>
<style type='text/css'>
ul {
  margin: 1ex;
}

li {
  border: 2px solid black;
  padding: 1ex;
}

ul.showing {
  display: block
}

ul.hidden {
  display: none
}

li.passed {
  background: #99FF66;
}

li.failed {
  background: #FF9999;
}
</style>
<script>
window.addEventListener('load', function(e) {
  var elts = document.getElementsByClassName('toggle');
  for (var i = 0; i < elts.length; i++) {
    var elt = elts[i];
    elt.addEventListener('click', (function(elt){
      return function(e) {
        var uls = elt.parentNode.getElementsByTagName("ul");
        for (var j = 0; j < uls.length; j++) {
          var ul = uls[j];
          if(ul.className === 'showing') ul.className = 'hidden';
          else ul.className = 'showing';
        }
        e.preventDefault();
      }
    })(elt));
  }
});
</script>
</head>

<body>
  <ul>
    %s
  </ul>
</body>
</html>
"""

def usage():
  print("""
    python all-tests.py <ie | sp> <dir1 dir2 ...>

      When run with no arguments, will run all the tests in ietestcenter
      and in sputnik_converted.

      If the first argument is ie, it will run the directories listed
      within the ietestcenter tests.  If the first argument is sp, it will
      run all the sputnik tests.
  """)

def dirTests(d):
  for chapter in os.listdir(d):
    f = open(os.path.join(result_dir, chapter + ".html"), "w")
    f2 = open(os.path.join(result_dir, chapter + ".result"), "w")
    result = testDir(os.path.join(d, chapter))
    f.write(template % result[0])
    f2.write("%s %s" % (result[1], result[2]))

def makeFrontPage():
  html = "<html><head></head><ul>%s</ul><div>Total: %s/%s</div></html>"
  l = ""
  totalS = 0
  totalF = 0
  for chapter in sorted(os.listdir(result_dir)):
    if chapter[-6:] == 'result':
      line = file(os.path.join(result_dir, chapter)).readline()
      if line: [success, fail] = line.split(" ")
      else: continue
      l += "<li><a href='%s.html'>%s</a> (%s/%s)</li>" % \
              (chapter[0:-7], chapter[0:-7], success, int(success)+int(fail))
      totalS += int(success)
      totalF += int(fail)

  summary = open(os.path.join(result_dir, 'summary.html'), "w")
  summary.write(html % (l, totalS, totalS + totalF))

def main(args):
  spiderMonkeyDir = 'test262/test/suite/sputnik_converted'
  ieDir = 'test262/test/suite/ietestcenter'
  try:
    os.mkdir(result_dir)
  except:
    # silent fail, the directory probably already existed
    pass

  if len(args) == 1:
    dirTests(spiderMonkeyDir)
    dirTests(ieDir)
  else:
    if (args[1] == "sp"): d = spiderMonkeyDir
    elif (args[1] == "ie"): d = ieDir
    elif (args[1] == "regen"): makeFrontPage(); return
    else:
      usage()
      return
    for chapter in args[2:]:
      f = open(os.path.join(result_dir, chapter + ".html"), "w")
      f2 = open(os.path.join(result_dir, chapter + ".result"), "w")
      result = testDir(os.path.join(d, chapter))
      f.write(template % result[0])
      f2.write("%s %s" % (result[1], result[2]))

  makeFrontPage()

main(sys.argv)
