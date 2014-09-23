#!/bin/python

import argparse
import os
import re

path = os.path

parser = argparse.ArgumentParser(description='generate report of test262 results')
parser.add_argument('--analyze', metavar='dir', type=str, nargs=1,
                   help='which directory will be analyzed')
parser.add_argument('--base', metavar='dir', type=str, nargs=1,
                   help='compared with which directory')

args = parser.parse_args()
curdir = path.abspath(path.curdir)
analyzedir = path.abspath(path.join(curdir, args.analyze[0]))
basedir = path.abspath(path.join(curdir, args.base[0]))

print analyzedir
print basedir

# get working directory, which locates at parents of current file's dir
workingdir = path.join(path.dirname(path.realpath(__file__)), path.pardir)
#os.chdir(workingdir)


failed_rexp = re.compile(r'(.*failed.*in.*mode)|(.*was expected to fail.*, but did.*)')
passed_rexp = re.compile(r'(.*passed.*in.*mode)|(.*failed in.*as expected)')
def passed(contents):
    if passed_rexp.match(contents) != None:
        return "passed"

    if failed_rexp.match(contents) != None:
        return "failed"

    return "NoTest"

# given .result files, compare each one with that of base dir
def analyze(file, analyzedir, basedir):
    """return (passed in analyzedir?, passed in basedir?, the two are the same?)"""
    analyzefile = path.join(analyzedir, file)
    basefile = path.join(analyzedir, file)
    # check if two files passed or failed test, if the two have
    # different result, ??
    assert(os.path.exists(analyzefile))
    with open(analyzefile) as f:
        analyze_content = f.read()
        analyze_status = passed(analyze_content)
    if not os.path.exists(basefile):
        base_status = "NotFound"
    else:
        with open(basefile) as f:
            base_content = f.read()
            base_status = passed(base_content)
    return (analyze_status, base_status, analyze_status == base_status)

def analyze_files(file_list):
    """return info for each file in a list that
      if it passed in analyzedir? passed in basedir? the results are the same?"""
    result = map(lambda f: (f,)+analyze(f, analyzedir, basedir), file_list)
    return result

# example
# ch: 'ch07-nonstrict' : 
# resultfiles:
#   [['file1', 'passed', 'passed', true],
#    ['file2', 'passed', 'NotFound, false]],
def walk(printer, dir):
    for dpath, dnames, fname in os.walk(dir):
        if dnames == []:
            ch = path.basename(dpath)
            resultfiles = [path.join(ch, f) for f in fname if f.endswith('result')]
            optinfofiles = [path.join(ch,f) for f in fname if f.endswith('optimizeinfo')]
            printer(ch, analyze_files(resultfiles))

# generate report
def status_printer(ch, status):
    print "\n\nsection: %s" % ch
    analyze_passed = len(filter(lambda x: x[1] == "passed", status))
    analyze_failed = len(filter(lambda x: x[1] == "failed", status))
    
    base_passed = len(filter(lambda x: x[2] == "passed", status))
    base_failed = len(filter(lambda x: x[2] == "failed", status))
    base_notfound = len(filter(lambda x: [2] == "NotFound", status))
    
    notthesame = len(filter(lambda x: [3] == False, status))
    
    analyzename = path.basename(analyzedir)
    basename = path.basename(basedir)
    print "%10s %15s %30s" % ("", analyzename, basename)
    print "%10s %15s %30s" % ("passed", analyze_passed, base_passed)
    print "%10s %15s %30s" % ("failed", analyze_failed, base_failed)
    if base_notfound != 0:
        print "%s are not found in %s" % (base_notfound, basename)
    if notthesame != 0:
        print "%s results are not the same" % nothesame

walk(status_printer, analyzedir)
