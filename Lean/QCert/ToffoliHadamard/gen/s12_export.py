"""Record the inputs of the emitters from the search results in work/:
data/micro.json (the relators and derivations Micro.lean needs, and the
involutions), data/routes.json (the pieces of the routes) and
data/rt_lrs.json (the Table 1 derivations of the round trip)."""
import json, pickle
from paths import work, data
from store import Store

S = Store.load(work("store4.pkl"))
(INV,) = pickle.load(open(work("phase1.pkl"), "rb"))
ROUTES, _rk = pickle.load(open(work("routes.pkl"), "rb"))
LRSD = pickle.load(open(work("rt_lrs.pkl"), "rb"))

# the relators Micro.lean uses: every base relator, and the closure of the
# Coxeter relations and the routes
targets = [i for i, n in enumerate(S.R.names)
           if n.startswith("far") or n.startswith("braid") or n.startswith("route_")]
need = set(); stack = list(targets)
while stack:
    r = stack.pop()
    if r in need:
        continue
    need.add(r)
    d = S.der[r]
    if d is not None:
        stack += [s[1] for s in d[2]]
keep = [r for r in range(len(S.R.rels)) if S.der[r] is None or r in need]
new = {r: k for k, r in enumerate(keep)}


def lines(key, items):
    return f'"{key}": [\n' + ",\n".join(json.dumps(x, separators=(",", ":")) for x in items) + "\n]"


rels = [list(S.R.rels[r]) for r in keep]
names = [S.R.names[r] for r in keep]
der = []
for r in keep:
    d = S.der[r]
    if d is None:
        der.append(None)
    else:
        u, v, st = d
        der.append([list(u), list(v), [[i, new[k], rot, cut, int(bool(rv))] for (i, k, rot, cut, rv) in st]])
inv = [[x, [[i, k, int(d)] for ((i, k, d), _w) in INV[x]]] for x in INV]
with open(data("micro.json"), "w", encoding="utf-8", newline="\n") as f:
    f.write("{\n" + ",\n".join([lines("rels", rels), lines("names", names), lines("der", der),
                                lines("inv", inv)]) + "\n}\n")


def piece(p):
    return [p[0], p[1]] if p[0] == "L" else [p[0], list(p[1])]


with open(data("routes.json"), "w", encoding="utf-8", newline="\n") as f:
    f.write("{\n" + lines("routes", [[x, [piece(p) for p in ROUTES[x]]] for x in ROUTES]) + "\n}\n")


def step(s):
    return [s[0]] + [int(x) if isinstance(x, bool) else x for x in s[1:]]


with open(data("rt_lrs.json"), "w", encoding="utf-8", newline="\n") as f:
    f.write("{\n" + lines("derivations", [[nm, [list(g) for g in a], [list(g) for g in b],
                                           [step(s) for s in st]] for nm, (a, b, st) in LRSD.items()])
            + "\n}\n")
print("kept", len(keep), "of", len(S.R.rels), "relators")
