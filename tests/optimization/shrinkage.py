"""calcualting shrinkage over the whole test suite"""
from parse import *

def average (lst):
    lst = filter(lambda l: l-0.0>0.05, lst)
    if len(lst) == 0:
        print 'debug: All zeros'
        return 0.0
    avg =  sum(lst)/len(lst)
    print "debug: %s-item list: %s. average: %s" % (len(lst), lst, avg) 
    return avg

filename = get_filename_from_cmd()
strict, nonstrict = parse_shrinkage(filename, mode=True)

print "strict:"
avg_strict = map(lambda lst: average(lst), strict)
print "nonstrict:"
avg_nonstrict = map(lambda lst: average(lst), nonstrict)
print "total:"
total = map(lambda lst: average(lst), \
            map (lambda pair: pair[0]+pair[1], zip(strict, nonstrict)))

header = """
           & Env     & User    & Total \\\\
\\hline
\\multirow{3}{*}{NAME}"""
template = "   & {0}   & {1:.2f} & {2:.2f} & {3:.2f} \\\\"

print header
print template.format("Strict", avg_strict[0], avg_strict[1], avg_strict[2])
print template.format("Nonstrict", avg_nonstrict[0], avg_nonstrict[1], avg_nonstrict[2])
print template.format("Total", total[0], total[1], total[2])


