"""calcualting correctness over the whole test suite"""
from parse import *

filename = get_filename_from_cmd()
xform, base= parse_correctness(filename)

print "transform: %s\nbase    : %s\ncorrect percentage: %.2f%%" % (xform, base, xform*100.0/base)
