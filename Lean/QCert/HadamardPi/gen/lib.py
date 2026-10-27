# A library of derived relations of Figure 6 on concrete indices, each found by the search of
# deriv.py (from a chain of intermediate words, or directly) and emitted as a Lean theorem checked
# by `derive_of`.  A lemma on m indices is available as a rewriting rule at every strictly
# increasing placement into the indices of a later lemma (`der_map`).
import itertools
from deriv import Engine, check_steps, lean_word, lean_steps, same_matrix, fmt, parse

class Lib:
    def __init__(self):
        self.lemmas = []   # (name, m, L, R)
        self.out = []

    def rules_for(self, m, use=None):
        rules = []
        for (name, k, L, R) in self.lemmas:
            if use is not None and name not in use: continue
            if k > m: continue
            for pl in itertools.combinations(range(m), k):
                f = dict(enumerate(pl))
                def mp(w):
                    return tuple((l[0],) + tuple(f[i] for i in l[1:]) for l in w)
                if list(pl) == list(range(k)) and k == m:
                    term = name
                else:
                    vec = ", ".join([f"({pl[0]} : Fin {m})"] + [str(i) for i in pl[1:]])
                    term = f"(der_map ![{vec}] (by decide) {name})"
                rules.append((term, mp(L), mp(R)))
        return rules

    def add(self, name, m, L, R, chain=None, use=None, maxd=6, maxlen=None, ins=None, doc=""):
        L, R = tuple(L), tuple(R)
        assert same_matrix(L, R, m), f"{name}: the two sides differ"
        eng = Engine(m, self.rules_for(m, use))
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
        self.lemmas.append((name, m, L, R))
        if doc: self.out.append(f"/-- {doc} -/")
        rhs = lean_word(R) if R else f"([] : List (Gen {m}))"
        lhs = lean_word(L) if L else f"([] : List (Gen {m}))"
        self.out.append(f"theorem {name} : Derivable Fig6 (ofList ({lhs} : List (Gen {m})))\n"
                        f"    (ofList {rhs}) :=\n  derive_of {lean_steps(st)} (by decide +kernel)\n")
        return st

    def text(self):
        return "\n".join(self.out)
