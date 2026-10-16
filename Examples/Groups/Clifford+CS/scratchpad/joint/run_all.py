# All the five-wire derivations, in order, into w5lib.L (five/load5.py
# imports this module and records every step).
#   python3 run_all.py
#
# RUN_PARTS (environment, comma-separated) selects what is run after the
# base (box ... f2 and the box lemmas (F1) needs), so that the slow parts
# can run in separate processes and be merged (five/merge5.py):
#   f1:P1+P2+..   the (F1) items by normal forms whose names start so
#   f1            all of them (every item but the de-borrowed ones and the
#                 four-wire rules)
#   f1big         cx-ccz and toff-ccz
#   deb           CS-K0/1, rel-269, rel-272 at the offsets 0, 1, by
#                 de-borrowing (TR2)
#   ckt2          ck-tct, by de-borrowing (TR2)
# The default is all of them, in this order; the last two are the
# derivations that use the transports TR2 (tr.py).
import os
import box, f5, boxsym, boxdash, boxbox, f0, f4, f4cs, f2
from w5lib import L

DEB = ['CS-K0@0', 'CS-K0@1', 'CS-K1@0', 'CS-K1@1', 'rel-269@0', 'rel-269@1', 'rel-272@0', 'rel-272@1']
F1_NF = [n for n, _, _ in __import__('f1rules').items()
         if not n.startswith(('cx-ccz', 'toff-ccz', 'ck-tct')) and n not in DEB]

box.build(L)
f5.build(L)
boxsym.build(L); boxsym.build_perms(L)
boxdash.build(L)
boxbox.build(L)
f0.build(L)
f4.build(L)
f4cs.build(L)
f2.build(L)

PARTS = [p for p in os.environ.get('RUN_PARTS', 'f1,f1big,deb,ckt2').split(',') if p]
if PARTS:
    import boxtoff, boxck, ssym
    boxtoff.build(L); boxck.build(L); ssym.build(L)
for part in PARTS:
    if part == 'f1' or part.startswith('f1:'):
        import f1
        only = F1_NF if part == 'f1' else [n for n in F1_NF if n.startswith(tuple(part[3:].split('+')))]
        f1.build(L, only=only)
    elif part == 'f1big':
        import f1big
        f1big.build(L, only=['cx-ccz@0', 'toff-ccz@0'])
    elif part == 'deb':
        import deb
        deb.build(L)
    elif part == 'ckt2':
        import ckt2
        ckt2.build(L)
    else:
        raise ValueError(part)
