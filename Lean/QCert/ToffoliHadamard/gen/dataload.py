"""Read the recorded inputs of the emitters (data/*.json)."""
import json
from paths import data
from store import Store


def micro():
    m = json.load(open(data("micro.json"), encoding="utf-8"))
    der = []
    for d in m["der"]:
        if d is None:
            der.append(None)
        else:
            u, v, st = d
            der.append((tuple(u), tuple(v), [(i, k, rot, cut, bool(rv)) for (i, k, rot, cut, rv) in st]))
    S = Store([tuple(r) for r in m["rels"]], m["names"], der)
    inv = {x: [(i, k, bool(d)) for (i, k, d) in st] for x, st in m["inv"]}
    return S, inv


def routes():
    r = json.load(open(data("routes.json"), encoding="utf-8"))["routes"]
    return {x: [(p[0], p[1]) if p[0] == "L" else (p[0], tuple(p[1])) for p in ps] for x, ps in r}


def rt_lrs():
    out = {}
    for nm, a, b, st in json.load(open(data("rt_lrs.json"), encoding="utf-8"))["derivations"]:
        steps = []
        for s in st:
            if s[0] == "P":
                steps.append(("P", s[1], s[2], bool(s[3])))
            else:
                steps.append(("R", s[1], s[2], s[3], s[4], bool(s[5])))
        out[nm] = ([tuple(g) for g in a], [tuple(g) for g in b], steps)
    return out
