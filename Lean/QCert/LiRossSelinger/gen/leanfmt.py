"""Lean syntax for words and steps."""
from macros import BASE

def gen_lit(g):
    """A generator on concrete indices (Fin m literal), proofs by decide."""
    if g[0] == 'n':
        return f"Gen.neg {g[1]}"
    if g[0] == 'x':
        return f"Gen.x {g[1]} {g[2]} (by decide)"
    return f"Gen.k {g[1]} {g[2]} {g[3]} {g[4]} (by decide) (by decide) (by decide)"

def word_lit(w):
    return "[" + ", ".join(gen_lit(g) for g in w) + "]"

def lt_proof(names, i, j):
    """Proof of names[i] < names[j] (i < j) from hyps h1..: h_{i+1} : names[i] < names[i+1]."""
    assert i < j
    hs = [f"h{t + 1}" for t in range(i, j)]
    p = hs[-1]
    for h in reversed(hs[:-1]):
        p = f"({h}.trans {p})"
    return p

def gen_sym(g, names):
    """A generator on symbolic indices names[i] (increasing), proofs from h1, h2, ..."""
    if g[0] == 'n':
        return f"Gen.neg {names[g[1]]}"
    if g[0] == 'x':
        return f"Gen.x {names[g[1]]} {names[g[2]]} {lt_proof(names, g[1], g[2])}"
    a, b, c, d = g[1:]
    return (f"Gen.k {names[a]} {names[b]} {names[c]} {names[d]} {lt_proof(names, a, b)} "
            f"{lt_proof(names, b, c)} {lt_proof(names, c, d)}")

def word_sym(w, names):
    return "[" + ", ".join(gen_sym(g, names) for g in w) + "]"

def step_r(st):
    f, ps, d, pos = st
    rev = 'true' if f.startswith('rev_') else 'false'
    fam = f[4:] if f.startswith('rev_') else f
    return f"⟨(.{fam}, {rev}), {list(ps)}, {'true' if d else 'false'}, {pos}⟩"

def step_d(st):
    f, ps, d, pos = st
    dd = 'true' if d else 'false'
    rev = 'true' if f.startswith('rev_') else 'false'
    fam = f[4:] if f.startswith('rev_') else f
    side = 'inr' if fam in BASE else 'inl'
    return f"⟨(.{side} .{fam}, {rev}), {list(ps)}, {dd}, {pos}⟩"

def steps_lit(sts, fmt):
    lines = []
    cur = []
    for s in sts:
        cur.append(fmt(s))
        if len(cur) == 4:
            lines.append(", ".join(cur)); cur = []
    if cur:
        lines.append(", ".join(cur))
    return "[" + ",\n      ".join(lines) + "]"
