import sys

def empty_section(text):
    return text.upper().find('EMPTY') != -1

def fetch(lines, prefix):
    prefix = prefix.upper()
    result = filter(lambda l: l.upper().find(prefix) != -1 or empty_section(l), lines)
    assert len(result) != 0
    return result

def get_mean(lines):
    def helper(line):
        lst = line.split(',')
        if len(lst) < 3:
            return 0.0
        else:
            return float(lst[2].strip().split(' ')[-1])
    return map(helper, lines)

def parse_correctness(filename):
    with open(filename) as f:
        passed = filter(lambda l: l.upper().startswith("PASS"), \
                          [l.strip() for l in f.readlines()])
        # get list of pairs  of (transformed, base)
        pair = [map(int,l.split()[1:]) for l in passed]
        x_passed= sum([l[0] for l in pair])
        base_passed = sum([l[1] for l in pair])
        return (x_passed, base_passed)
                            
def parse_shrinkage(filename, mode=False):
    """return data grouped by chapters.
       if mode is false, return (float list, float list, float list)
       else, return a pair of (float list, float list, float list)
    """
    def get_strict_lines(lines):
        """get lines that belong to strict mode"""
        return filter(lambda l: l.upper().find('NON') == -1 or empty_section(l), lines)

    def get_nonstrict_lines(lines):
        """get lines that belong to nonstrict mode"""
        return filter(lambda l: l.upper().find("NON") != -1 or empty_section(l), lines)

    with open(filename) as f:
        contents = filter(lambda l: l != "", [l.strip() for l in f.readlines()])
        if mode == False:
            env_data = get_mean(fetch(contents, "env"))
            usr_data = get_mean(fetch(contents, "usr"))
            total_data = get_mean(fetch(contents, "total"))
            assert(len(env_data) == len(usr_data))
            assert(len(usr_data) == len(total_data))
            return env_data, usr_data, total_data
        else:
            strict = map(lambda n: get_mean(get_strict_lines(fetch(contents, n))), ["env", "usr", "total"])
            
            nonstrict = map(lambda n: get_mean(get_nonstrict_lines(fetch(contents, n))), ["env", "usr", "total"])
            return strict, nonstrict


def max_and_min(lst):
    return max(lst), \
           min(filter(lambda x: x!=0, lst))


def get_filename_from_cmd():
    if len(sys.argv) < 2:
        print "%s [datafile]\n" % sys.argv[0]
        exit(1)
    else:
        return sys.argv[1]
