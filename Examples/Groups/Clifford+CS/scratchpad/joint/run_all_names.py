# The (F1) item names of run_all's parts, without running anything.
import f1rules
DEB = ['CS-K0@0', 'CS-K0@1', 'CS-K1@0', 'CS-K1@1', 'rel-269@0', 'rel-269@1', 'rel-272@0', 'rel-272@1']
F1_NF = [n for n, _, _ in f1rules.items()
         if not n.startswith(('cx-ccz', 'toff-ccz', 'ck-tct')) and n not in DEB]
