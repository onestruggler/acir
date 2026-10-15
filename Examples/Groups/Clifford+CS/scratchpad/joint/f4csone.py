import sys, traceback
import derivn, box, boxsym, boxdash, boxbox, f4cs
derivn.QUIET = True
L = box.build({}); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
i, j = int(sys.argv[1]), int(sys.argv[2])
try:
    f4cs.direct(L, i, j); print('ok')
except Exception:
    traceback.print_exc()
