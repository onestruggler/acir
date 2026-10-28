from paths import work, data, module
import sys, time, pickle
from model import *
from rels import FIG4, FIG7, RK
from search import RuleSet, bidir, replay

def enc_w(ws):
    return bytes(IDX[x] for x in ws)

def dec_w(b):
    return [LET[i] for i in b]

rs = RuleSet()
for n, l, r in FIG4:
    rs.add(enc_w(l), enc_w(r), f"r{n}")
rs.add(enc_w(["Kc", "Kc"]), b"", "r84")

lemmas = {}
order = ["X0", "CX01", "K12", "CCX12", "K01", "Kc",
         "CX10", "CZ01", "Z0", "Z1", "CX21", "CX12", "S12", "S01", "CX02", "CX20", "S02",
         "CCX02", "CCX01", "X1", "X2", "Z2", "CZ02", "CZ12"]
todo = list(order)
for extra in (2, 4, 6, 8):
  progress = True
  while progress:
    progress = False
    for x in list(todo):
        t = time.time()
        res = bidir(rs, enc_w([x, x]), b"", maxlen=2 + extra, limit=300_000)
        if res is None:
            continue
        todo.remove(x); progress = True
        print(x, len(res), "steps", round(time.time() - t, 2), "s", extra)
        assert replay(rs, enc_w([x, x]), res) == b""
        lemmas[x] = res
        rs.add(enc_w([x, x]), b"", f"inv_{x}")
print("left", todo)
if False:
    for x in []:
        pass

pickle.dump((lemmas,), open(work("phase1.pkl"), "wb"))
