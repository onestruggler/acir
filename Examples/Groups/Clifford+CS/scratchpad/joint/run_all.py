# All the five-wire derivations, in order, into w5lib.L (five/load5.py
# imports this module and records every step).
#   python3 run_all.py
import box, f5
from w5lib import L

box.build(L)
f5.build(L)
