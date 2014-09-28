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

def parse_opt_info(filepath):
    """return [(phase name, count), (phase name2, count2)...]"""
    result = []
    with open(filepath) as f:
        contents = f.readlines()
        for line in contents:
            if line.strip() == "":
                continue
            try:
                name, opt = line.strip().split(':')
                result.append([name.strip(), opt.strip()])
            except:
                pass
    return result

def analyze_files(file_list):
    """return info for each file in a list that
      if it passed in analyzedir? passed in basedir? the results are the same?"""
    result = map(lambda f: (f,)+analyze(f, analyzedir, basedir), file_list)
    return result

def parse_opt_files(file_list):
    """result [filename, [[phase1, count], [phase2, count], ...]]"""
    file_list = map(lambda f: path.join(analyzedir, f), file_list)
    result = map(lambda f: [f, parse_opt_info(f)], file_list)
    return result

# example
# ch: 'ch07-nonstrict' : 
# resultfiles:
#   [['file1', 'passed', 'passed', true],
#    ['file2', 'passed', 'NotFound, false]],
def walk_result(printer, dir):
    for dpath, dnames, fname in os.walk(dir):
        if dnames == []:
            ch = path.basename(dpath)
            resultfiles = [path.join(ch, f) for f in fname if f.endswith('result')]
            printer(ch, analyze_files(resultfiles))

def walk_optimizeinfo(printer, dir):
    for dpath, dnames, fname in os.walk(dir):
        if dnames == []:
            ch = path.basename(dpath)
            opt_files = [path.join(ch, f) for f in fname if f.endswith('optimizeinfo')]
            printer(ch, parse_opt_files(opt_files))

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

def opt_info_printer(ch, files):
    def print_config(contents):
        args = filter(lambda arg: arg.startswith('-count-nodes') or 
                                    arg.startswith('-opt-'), contents.strip().split(' '))
        index = 1
        phase = []
        for arg in args:
            arg = arg.strip()
            if arg == "-count-nodes":
                print "phase %d:" % index,
                if phase == []:
                    print "no optimization"
                else:
                    print " ".join(phase)
                phase = []
                index += 1
            else:
                phase.append(arg)
        print ""
            
    
    # print config file
    config = path.join(analyzedir, 'config.txt')
    assert(path.exists(config))

    
    with open(config) as f:
        print "config:"
        print_config(f.read())

    print "section: %s\n" % ch
    if files == []:
        print "%s is empty. Those tests may be only for either strict or nonstrict mode\n\n" % ch
        print "-----\n\n"
        return

    # print title
    file, phases = files[0]
    print "%25s " % "file",
    for index, (name, count) in enumerate(phases):
        print "%10s " % ("phase " + str(index+1)),
    print "%10s" % "improve",
    print ""
    
    # print file info
    for info in files:
        file, phases = info
        print "%25s" % path.splitext(path.basename(file))[0],
        phases = map(lambda x: x[1], phases)
        for phase in phases:
            print "%10s " % phase,
        if phases == []:
            print ""
            continue
        print "%10s%%" % round(((int(phases[0])-int(phases[-1]))/float(phases[0])) * 100, 1),
        print ""
        
    print "-----\n\n"

#walk_result(status_printer, analyzedir)
walk_optimizeinfo(opt_info_printer, analyzedir)
