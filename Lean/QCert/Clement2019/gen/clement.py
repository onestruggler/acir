# Clement's relations (1)-(21) on m concrete indices, as rewriting rules for the bidirectional
# search of HadamardPi/gen/deriv.py, and emission of Lean `CStep` lists for
# `QCert.Clement2019.deriveC_of` (Check.lean).
# Letters: ('Z',a), ('X',a,b), ('H',a,b) with a != b in either order (Clement's generators).
# Words are tuples in written order, as in deriv.py.
import itertools, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'HadamardPi', 'gen'))
import deriv
from deriv import fmt, check_steps
from q2 import matrix


def Z(a): return ('Z', a)
def X(a, b): assert a != b; return ('X', a, b)
def H(a, b): assert a != b; return ('H', a, b)


def parse(s):
    """'H20 X13 Z2' -> word (indices are single digits)"""
    out = []
    for t in s.split():
        if t[0] == 'Z': out.append(Z(int(t[1:])))
        else: out.append((t[0], int(t[1]), int(t[2])))
    return tuple(out)


def L20(a, b, c, d):
    return (H(a, b), H(a, c), H(b, d), H(a, b), Z(a), Z(b), H(a, c), H(b, d))
def R20(a, b, c, d):
    return (H(a, c), H(b, d), H(a, b), Z(a), Z(b), H(a, c), H(b, d), H(a, b))
def L21(a, b, c, d, e, f):
    return (H(a, b), H(a, c), H(b, d), H(a, e), H(b, f), H(a, b), Z(a), Z(b), H(a, e), H(b, f),
            H(a, c), H(b, d))
def R21(a, b, c, d, e, f):
    return (H(a, c), H(b, d), H(a, e), H(b, f), H(a, b), Z(a), Z(b), H(a, e), H(b, f), H(a, c),
            H(b, d), H(a, b))


def crules(m, full=True, tags=None):
    """All instances (tag, ix, L, R) of Clement's relations (1)-(19), and (20), (21) at every
    injective placement when `full`, on m indices.  `ix` lists the indices in the order of the
    Lean constructor (j, k, l, t for (1)-(19); the placement for (20), (21))."""
    out = []
    R = range(m)
    want = (lambda t: True) if tags is None else (lambda t: t in tags)
    for j in R:
        out.append(('t1', (j,), (Z(j), Z(j)), ()))
    for j, k in itertools.permutations(R, 2):
        out.append(('t2', (j, k), (H(j, k), H(j, k)), ()))
        out.append(('t3', (j, k), (X(j, k), X(j, k)), ()))
        out.append(('t4', (j, k), (Z(j), Z(k)), (Z(k), Z(j))))
        out.append(('t10', (j, k), (X(j, k), Z(k)), (Z(j), X(j, k))))
        out.append(('t11', (j, k), (X(j, k), Z(j)), (Z(k), X(j, k))))
        out.append(('t16', (j, k), (Z(j), Z(k), X(j, k)), (X(j, k), Z(j), Z(k))))
        out.append(('t17', (j, k), (Z(j), Z(k), H(j, k)), (H(j, k), Z(j), Z(k))))
        out.append(('t18', (j, k), (H(j, k), X(j, k)), (Z(k), H(j, k))))
    for j, k, l in itertools.permutations(R, 3):
        out.append(('t5', (j, k, l), (Z(l), H(j, k)), (H(j, k), Z(l))))
        out.append(('t6', (j, k, l), (Z(l), X(j, k)), (X(j, k), Z(l))))
        out.append(('t12', (j, k, l), (X(j, k), X(j, l)), (X(k, l), X(j, k))))
        out.append(('t13', (j, k, l), (X(j, k), X(l, j)), (X(l, k), X(j, k))))
        out.append(('t14', (j, k, l), (X(j, k), H(j, l)), (H(k, l), X(j, k))))
        out.append(('t15', (j, k, l), (X(j, k), H(l, j)), (H(l, k), X(j, k))))
    for j, k, l, t in itertools.permutations(R, 4):
        out.append(('t7', (j, k, l, t), (H(j, k), H(l, t)), (H(l, t), H(j, k))))
        out.append(('t8', (j, k, l, t), (H(j, k), X(l, t)), (X(l, t), H(j, k))))
        out.append(('t9', (j, k, l, t), (X(j, k), X(l, t)), (X(l, t), X(j, k))))
        out.append(('t19', (j, k, l, t), (H(j, k), H(l, t), H(j, l), H(k, t)),
                    (H(j, l), H(k, t), H(j, k), H(l, t))))
    if full:
        for ix in itertools.permutations(R, 4):
            out.append(('t20', ix, L20(*ix), R20(*ix)))
        for ix in itertools.permutations(R, 6):
            out.append(('t21', ix, L21(*ix), R21(*ix)))
    return [r for r in out if want(r[0])]


def increasing(w):
    return all(l[0] == 'Z' or l[1] < l[2] for l in w)


class CEngine(deriv.Engine):
    """deriv.Engine over Clement's relations.  `use`: restrict tags; `inc`: only rules whose
    letters all have increasing indices; `lemmas`: (Lean term, L, R)."""
    def __init__(self, m, lemmas=(), use=None, full=True, inc=False):
        self.m = m
        self.rs = []
        for (t, ix, L, R) in crules(m, full, use):
            if inc and not (increasing(L) and increasing(R)): continue
            self.rs.append((('rel', t, ix), L, R))
        for (name, L, R) in lemmas:
            if inc and not (increasing(L) and increasing(R)): continue
            self.rs.append((('lem', name), tuple(L), tuple(R)))
        self.idx = {}
        self.ins = []
        for r in self.rs:
            key, L, R = r
            for fwd, S, T in ((True, L, R), (False, R, L)):
                if len(S) == 0:
                    self.ins.append((key, fwd, S, T))
                else:
                    self.idx.setdefault(S[0], []).append((key, fwd, S, T))


def same_matrix(u, v, m):
    return matrix(list(u), m) == matrix(list(v), m)


def lean_letter(l):
    if l[0] == 'Z': return f"cz {l[1]}"
    return f"c{l[0].lower()} {l[1]} {l[2]}"


def lean_word(w, m):
    if not w:
        return f"([] : List (Gen {m}))"
    return "([" + ", ".join(lean_letter(l) for l in w) + f"] : List (Gen {m}))"


def lean_steps(steps, per_line=3, indent="    "):
    items = []
    for key, i, fwd in steps:
        f = "true" if fwd else "false"
        if key[0] == 'rel':
            items.append(f".rel .{key[1]} [{', '.join(map(str, key[2]))}] {i} {f}")
        else:
            items.append(f".lem _ _ {key[1]} {i} {f}")
    lines = []
    for k in range(0, len(items), per_line):
        lines.append(indent + ", ".join(items[k:k + per_line]))
    return "[" + (",\n".join(lines)).lstrip() + "]"


class CLib:
    """Derived Clement relations on concrete indices, each available at every injective
    placement into the indices of a later lemma (`derC_map`).  A lemma is derived in
    `RelK true` (using (20), (21)) when `full`, in `RelK false` (only (1)-(19)) otherwise; a
    `RelK false` lemma enters a `RelK true` derivation through `liftK`."""
    def __init__(self):
        self.lemmas = []     # (name, m, L, R, full)
        self.out = []
        self.placed = {}     # Lean name -> (lemma, k, m, placement)
        self.emitted = set()

    def flag(self, name):
        return next(lf for (n2, _, _, _, lf) in self.lemmas if n2 == name)

    def rules_for(self, m, full, use=None, inc=False):
        rules = []
        for (name, k, L, R, lf) in self.lemmas:
            if use is not None and name not in use: continue
            if lf and not full: continue
            if k > m: continue
            # with `inc`, only increasing placements (as HadamardPi's Lib); otherwise all
            places = itertools.combinations(range(m), k) if inc else itertools.permutations(range(m), k)
            for pl in places:
                f = dict(enumerate(pl))
                def mp(w):
                    return tuple((l[0],) + tuple(f[i] for i in l[1:]) for l in w)
                Lp, Rp = mp(L), mp(R)
                if inc and not (increasing(Lp) and increasing(Rp)): continue
                if list(pl) == list(range(k)) and k == m:
                    term = name
                else:
                    term = f"{name}_at{''.join(map(str, pl))}_{m}"
                    self.placed[term] = (name, k, m, pl)
                rules.append((term, Lp, Rp))
        return rules

    def add(self, name, m, L, R, chain=None, use=None, uselem=None, maxd=6, maxlen=None, ins=None,
            doc="", full=True, inc=False):
        L, R = tuple(L), tuple(R)
        assert same_matrix(L, R, m), f"{name}: the two sides differ"
        eng = CEngine(m, self.rules_for(m, full, uselem, inc), use, full, inc)
        kw = dict(maxd=maxd)
        if maxlen is not None: kw['maxlen'] = maxlen
        if ins is not None: kw['ins_letters'] = set(ins)
        if chain is None:
            st = eng.search(L, R, **kw)
            if st is None: raise ValueError(f"{name}: no derivation found")
        else:
            words = [L] + [tuple(w) for w in chain] + [R]
            for u, v in zip(words, words[1:]):
                assert same_matrix(u, v, m), f"{name}: chain step {fmt(u)} / {fmt(v)} differs"
            st = eng.chain(words, **kw)
        check_steps(st, L, R, eng)
        self.lemmas.append((name, m, L, R, full))
        fl = "true" if full else "false"
        st2 = []
        for (key, i, fwd) in st:
            if key[0] == 'lem':
                term = key[1]
                if term in self.placed and term not in self.emitted:
                    self.emitted.add(term)
                    (nm, k, mm, pl) = self.placed[term]
                    vec = ", ".join([f"({pl[0]} : Fin {mm})"] + [str(j) for j in pl[1:]])
                    f = dict(enumerate(pl))
                    Lk, Rk = next((a, b) for (n2, k2, a, b, _) in self.lemmas if n2 == nm)
                    def mp(w):
                        return tuple((l[0],) + tuple(f[j] for j in l[1:]) for l in w)
                    lfl = "true" if self.flag(nm) else "false"
                    self.out.append(
                        f"theorem {term} : Derivable (RelK {lfl}) (ofList {lean_word(mp(Lk), mm)})\n"
                        f"    (ofList {lean_word(mp(Rk), mm)}) :=\n"
                        f"  derC_map (m := {k}) ![{vec}] (by decide) {nm}\n")
                base = self.placed[term][0] if term in self.placed else term
                if self.flag(base) != full:
                    term = f"(liftK {term})"
                st2.append((('lem', term), i, fwd))
            else:
                st2.append((key, i, fwd))
        if doc: self.out.append(f"/-- {doc} -/")
        self.out.append(f"theorem {name} : Derivable (RelK {fl}) (ofList {lean_word(L, m)})\n"
                        f"    (ofList {lean_word(R, m)}) :=\n"
                        f"  deriveC_of {lean_steps(st2)} (by decide +kernel)\n")
        return st

    def text(self):
        return "\n".join(self.out)
