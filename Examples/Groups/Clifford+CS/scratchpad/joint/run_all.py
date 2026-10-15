# All the five-wire derivations, in order, into w5lib.L (five/load5.py
# imports this module and records every step).
#   python3 run_all.py
import box, f5, boxsym, boxdash, boxbox, f0, f4, f4cs
from w5lib import L

box.build(L)
f5.build(L)
boxsym.build(L); boxsym.build_perms(L)
boxdash.build(L)
boxbox.build(L)
f0.build(L)
f4.build(L)
f4cs.build(L)
