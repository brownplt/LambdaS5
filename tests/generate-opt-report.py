import re

# this script takes 'log' file produced by optimization_all_tests.sh
# and produces report on optimization

class TestCase:
    def __init__(self, name, pre, after, result):
        self.name = name
        self.pre = pre
        self.after = after
        if result:
            self.result = result
        else:
            self.result = "passed"
        
    def as_one_line(self):
        print "%40s %10s %10s %10s" % (self.name, self.pre, self.after, self.result)

if __name__ == '__main__':
    name = "log"
    f = open(name)
    contents = f.readlines()
    testcases = []
    name = None
    pre = None
    after = None
    result = None

    progress = "name" # status can be name, pre, after, result
    for content in contents:
        if content.startswith('optimize'): # if content startswith optimize, status should be "start" again
            if progress != "name" and progress != "pre" and progress != "result":
                print "unexpected content: %s when progress=%s" % (content, progress)
                assert 0 == 1
            else:                
                if progress == "result":
                    testcases.append(TestCase(name, pre, after, result))
                # start
                pre = None
                after = None
                name = None
                result = None

                print "get name %s" % content
                name = re.findall('/(.[a-zA-z0-9-\.]*\.js)', content)[0]
                progress = "pre"
                print "get name %s" % name
            continue

        if progress == "pre" or progress == "after":
            assert name != None
            num = re.findall('^[0-9]+', content)
            if num != []:
                num = num[0]
                if progress == "pre":
                    assert after == None
                    pre = num
                    print "get pre %s" % pre
                    progress = "after"
                    continue
                if progress == "after":
                    assert result == None
                    after = num
                    print "get after %s" % after
                    progress = "result"
                    continue
            continue

        if progress == "result" and re.findall("^passed|^failed", content, re.I) != []:
            assert name != None and pre != None and after != None
            result = content.strip().strip('!."').lower()
            print "result %s" % result
            continue

    if progress == "result":
        testcases.append(TestCase(name, pre, after, result))
    
    for t in testcases:
        t.as_one_line()
            
        
