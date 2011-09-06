import os
import subprocess
import time
import sys

timeout_seconds = 4

def testFile(f):
  p = subprocess.Popen(["./single-test.sh", str(f)],
                       stdin=subprocess.PIPE,
                       stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE,
                       cwd=".")
  start = time.clock()
  while(True):
    now = time.clock()
    p.poll()
    if (p.returncode is None) and (now - start > timeout_seconds):
      p.kill()
      return ("<li class='failed'>%s (Terminated)</li>" % str(f), 0, 1)
    elif (not p.returncode is None):
      if p.returncode == 0:
        return ("<li class='passed'>%s</li>" % str(f), 1, 0)
      else:
        return ("<li class='failed'>%s (Failed)</li>" % str(f), 0, 1)

  raise Exception("BLOWNUP")

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

for chapter in sys.argv[1:]:
  f = open("testresults/" + chapter, "w")
  f.write(template % testDir("test262/test/suite/ietestcenter/" + chapter)[0])

