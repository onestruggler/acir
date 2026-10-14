#!/usr/bin/env python3
"""Proof-producing coset enumeration for the natural CCX+HH rules.

Letters at width w are the placed gates (X i, CX i, CCX i, HH i); the
macros XC i = HH i CX i HH i and Ex i = CX i XC i CX i are expanded.
The axioms at width w are the natural rules (Natural/Syntactics.agda) at
every placement that fits, the involutions, and the commutations of
gates on disjoint wires.
"""
import sys, time
import core as C
import proofs as P

RULES = [  # (Agda name, lhs, rhs), on the bottom wires
    ("X-control", "X1 CX0 X1", "CX0 X0"),
    ("X-controlᵣ", "XC0 X0 XC0", "X0 X1"),
    ("CNOT-S3", "CX0 XC0 CX0 XC0 CX0 XC0", ""),
    ("X-Z", "X0 HH0 X1 HH0", "HH0 X1 HH0 X0"),
    ("braid", "Ex0 Ex1 Ex0", "Ex1 Ex0 Ex1"),
    ("CX-up", "Ex0 Ex1 CX0 Ex1 Ex0", "CX1"),
    ("CCX-sym", "Ex1 CCX0 Ex1", "CCX0"),
    ("CCX-neg", "X1 CCX0 X1", "CCX0 Ex1 CX0 Ex1"),
    ("CCX-XC", "CCX0 XC0 CCX0 XC0", "Ex0 CCX0 Ex0 CCX0"),
    ("HH-swap₀", "Ex0 HH1 Ex0", "HH0 HH1"),
    ("HH-swap₁", "Ex1 HH0 Ex1", "HH0 HH1"),
    ("CCX-HH", "CCX0 XC0 HH0 XC0", "XC0 HH0 XC0 CCX0"),
    ("CCX-comm", "CCX1 CX0 CCX1 CX0", "Ex0 CCX1 Ex0"),
    ("CCX-up", "Ex0 Ex1 Ex2 CCX0 Ex2 Ex1 Ex0", "CCX1"),
]

def expand(gs, text, shift):
    out = []
    for tok in text.split():
        base, i = C.split_name(tok)
        i += shift
        if base == "XC":
            out += [f"HH{i}", f"CX{i}", f"HH{i}"]
        elif base == "Ex":
            out += [f"CX{i}", f"HH{i}", f"CX{i}", f"HH{i}", f"CX{i}"]
        else:
            out.append(f"{base}{i}")
    return tuple(gs.index[t] for t in out)

def axioms(gs):
    out = []
    for name, l, r in RULES:
        for s in range(gs.n):
            try:
                out.append(P.Axiom((name, s), expand(gs, l, s), expand(gs, r, s)))
            except KeyError:
                break
    for g in range(len(gs.names)):
        out.append(P.Axiom(("inv", g), (g, g), ()))
    for a in range(len(gs.names)):
        for b in range(len(gs.names)):
            if a < b and not set(gs.wires[a]) & set(gs.wires[b]):
                out.append(P.Axiom(("comm", a, b), (b, a), (a, b)))
    return out

if __name__ == "__main__":
    w = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    gs = C.GateSet(w)
    ax = axioms(gs)
    t = time.time()
    tc = P.ProofTC(len(gs.names), ax)
    live = tc.run()
    print(f"width {w}: {len(ax)} axioms, {len(live)} live cosets of {len(tc.rep)} defined, "
          f"{len(tc.facts)} facts ({time.time()-t:.1f}s)")
    finals = {(c, y): tc.final(c, y) for c in live for y in range(len(gs.names))}
    bad = [k for k, f in enumerate(tc.facts) if not P.replay(tc, f)]
    print(f"replay: {len(tc.facts) - len(bad)} of {len(tc.facts)} facts check")
    if bad:
        f = tc.facts[bad[0]]
        print("first bad:", bad[0], gs.show(f.lhs), "->", gs.show(f.rhs), f.steps[:6])
    rep = C.PermRep(gs)
    sems = {rep.evaluate(tc.rep[c]) for c in live}
    print("distinct semantics of the live representatives:", len(sems))
    print("max representative length:", max(len(tc.rep[c]) for c in live),
          " max steps in a final fact:", max(len(tc.facts[f].steps) for _, f in finals.values()))
