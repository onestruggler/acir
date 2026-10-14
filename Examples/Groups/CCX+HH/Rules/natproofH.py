#!/usr/bin/env python3
"""Proof-producing coset enumeration for the natural CCX+H rules.

As natproof.py, for the gate set {X, CX, CCX, H} (coreH.GateSetH): the
rules of CCX+H/Natural/Syntactics.agda at every placement that fits, the
involutions, and the commutations of gates on disjoint wires.  The
macros: XC i = H i H i+1 CX i H i+1 H i (the reversed CNOT), Ex i =
CX i XC i CX i (the swap), CZ i = H i CX i H i, Z i = H i X i H i.
"""
import sys, time
import core as C
import coreH as H
import proofs as P

RULES = [  # (Agda name, lhs, rhs), on the bottom wires
    ("XH⁸", "X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0", ""),
    ("X-controlᵣ", "XC0 X0 XC0", "X0 X1"),
    ("H-swap", "Ex0 H0 Ex0", "H1"),
    ("CZ-XC", "CZ0 XC0 CZ0 XC0", "Z0"),
]

MACROS = {
    "XC": lambda i: [f"H{i}", f"H{i+1}", f"CX{i}", f"H{i+1}", f"H{i}"],
    "Ex": lambda i: [f"CX{i}", f"H{i}", f"H{i+1}", f"CX{i}", f"H{i+1}", f"H{i}", f"CX{i}"],
    "CZ": lambda i: [f"H{i}", f"CX{i}", f"H{i}"],
    "Z": lambda i: [f"H{i}", f"X{i}", f"H{i}"],
}


def expand(gs, text, shift):
    out = []
    for tok in text.split():
        base, i = C.split_name(tok)
        i += shift
        out += MACROS[base](i) if base in MACROS else [f"{base}{i}"]
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
    gs = H.GateSetH(w)
    ax = axioms(gs)
    t = time.time()
    tc = P.ProofTC(len(gs.names), ax)
    live = tc.run()
    print(f"width {w}: {len(ax)} axioms, {len(live)} live cosets of {len(tc.rep)} defined, "
          f"{len(tc.facts)} facts ({time.time()-t:.1f}s)")
    bad = [k for k, f in enumerate(tc.facts) if not P.replay(tc, f)]
    print("bad replays:", len(bad))
