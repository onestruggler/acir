# A checker for derivations of 4-wire identities, step by step.
#
# Words are lists of macro gates: the generators S, K, CS, iI and their
# inverses, X, Z, CZ, CX, SWAP, CK, and the three-wire CCZ and Toffoli
# (expanded to the Agda spellings for the semantics).  A step is
#
#   win  : rewrite a contiguous window whose gates lie on <= 3 wires to
#          any word on the same wires with the same operator (one
#          Lemma 5.1 step given completeness on three wires);
#   comm : exchange two adjacent gates on disjoint wires (structural);
#   delta: the four-wire rule CX_{a->b} CCZ_{b,u,v} CX_{a->b}
#          = CCZ_{b,u,v} CCZ_{a,u,v}, at any placement, either way
#          (one rule instance plus the swap network to place it);
#   lemma: a previously checked identity, at a position, either way.
#
# Every step is checked semantically (fingerprints over F_p) and for
# its legality, so a finished derivation is a derivation of the circuit
# theory with the schema.
import sys
from itertools import combinations
from prover2 import apply as apply_basic, P, I, GINV, DIM, VECS

def CCZw(a, b, c):
    return [('CS', b, c), ('CX', a, b), ('CSd', b, c), ('CX', a, b), ('SWAP', b, c), ('CS', a, b), ('SWAP', b, c)]
def TOFFw(t, b, c):
    return [('K', t)] + CCZw(t, b, c) + [('Kd', t)]

def expand(word):
    out = []
    for g in word:
        if g[0] == 'CCZ': out += CCZw(*g[1:])
        elif g[0] == 'TOFF': out += TOFFw(*g[1:])
        else: out.append(g)
    return out

def fp(word):
    out = []
    for v in VECS:
        for op in reversed(expand(word)): v = apply_basic(op, v)
        out.extend(v)
    return tuple(out)

def support(g): return frozenset(g[1:])
def supp(word): return frozenset().union(*(support(g) for g in word)) if word else frozenset()

INV = {'iI': 'iIi', 'iIi': 'iI', 'S': 'Sd', 'Sd': 'S', 'K': 'Kd', 'Kd': 'K', 'CS': 'CSd', 'CSd': 'CS',
       'CK': 'CKd', 'CKd': 'CK', 'X': 'X', 'Z': 'Z', 'CZ': 'CZ', 'CX': 'CX', 'SWAP': 'SWAP',
       'CCZ': 'CCZ', 'TOFF': 'TOFF'}
def inv(word): return [(INV[g[0]],) + g[1:] for g in reversed(word)]

def show(word): return ' '.join(g[0] + ''.join(str(w) for w in g[1:]) for g in word)

class Derivation:
    def __init__(self, name, lhs, rhs, lemmas=None):
        self.name, self.lhs, self.rhs = name, list(lhs), list(rhs)
        self.cur = list(lhs); self.steps = []; self.lemmas = lemmas or {}
        assert fp(self.lhs) == fp(self.rhs), f'{name}: not semantically valid'

    def _set(self, new, kind, info):
        assert fp(new) == fp(self.cur), f'{self.name}: step {kind} {info} changes the operator'
        self.steps.append((kind, info, list(self.cur), list(new))); self.cur = new

    def win(self, i, j, rep):
        w = self.cur[i:j]; s = supp(w) | supp(rep)
        assert len(s) <= 3, f'{self.name}: window {show(w)} -> {show(rep)} on {sorted(s)} is not on three wires'
        assert fp(w) == fp(rep), f'{self.name}: window {show(w)} and {show(rep)} differ'
        self._set(self.cur[:i] + list(rep) + self.cur[j:], 'win', (i, j, show(w), show(rep)))

    def comm(self, i):
        g, h = self.cur[i], self.cur[i + 1]
        assert not (support(g) & support(h)), f'{self.name}: {show([g])} and {show([h])} are not disjoint'
        self._set(self.cur[:i] + [h, g] + self.cur[i + 2:], 'comm', i)

    def delta(self, i, forward=True):
        """forward: CX_ab CCZ_buv CX_ab  ->  CCZ_buv CCZ_auv at position i; backward the reverse."""
        if forward:
            cx, ccz, cx2 = self.cur[i:i + 3]
            assert cx[0] == 'CX' and cx2 == cx and ccz[0] == 'CCZ', f'{self.name}: no CX CCZ CX at {i}'
            a, b = cx[1], cx[2]
            assert b in ccz[1:] and a not in ccz[1:], f'{self.name}: delta needs the target in the CCZ, the control off it'
            u, v = [w for w in ccz[1:] if w != b]
            rep = [('CCZ', b, u, v), ('CCZ', a, u, v)]
            self._set(self.cur[:i] + rep + self.cur[i + 3:], 'delta', (i, show(self.cur[i:i + 3]), show(rep)))
        else:
            c1, c2 = self.cur[i:i + 2]
            assert c1[0] == 'CCZ' and c2[0] == 'CCZ', f'{self.name}: no CCZ CCZ at {i}'
            s1, s2 = set(c1[1:]), set(c2[1:])
            common = s1 & s2
            assert len(common) == 2, f'{self.name}: the two CCZs must share two wires'
            (b,) = tuple(s1 - common); (a,) = tuple(s2 - common); u, v = sorted(common)
            rep = [('CX', a, b), ('CCZ', b, u, v), ('CX', a, b)]
            self._set(self.cur[:i] + rep + self.cur[i + 2:], 'delta⁻¹', (i, show(self.cur[i:i + 2]), show(rep)))

    def lemma(self, name, i, forward=True):
        l, r = self.lemmas[name]
        src, dst = (l, r) if forward else (r, l)
        assert self.cur[i:i + len(src)] == list(src), f'{self.name}: lemma {name} does not match at {i}: {show(self.cur[i:i+len(src)])}'
        self._set(self.cur[:i] + list(dst) + self.cur[i + len(src):], 'lemma', (name, i, forward))

    def done(self):
        assert self.cur == self.rhs, f'{self.name}: not finished: at {show(self.cur)}, want {show(self.rhs)}'
        print(f'ok   {self.name}: {len(self.steps)} steps', flush=True)
        self.lemmas[self.name] = (self.lhs, self.rhs)
        return self.lemmas

def ccz_sym(a, b, c, a2, b2, c2):
    """CCZ is symmetric: a 3-wire window step (checked by the caller)."""
    return [('CCZ', a, b, c)], [('CCZ', a2, b2, c2)]

if __name__ == '__main__':
    L = {}
    # Lemma 1: CZ_03 conjugates the Toffoli T = Toff(0;1,2) to T . CCZ_123
    #   T CZ_03 T = CCZ_123 CZ_03, via K_0 D K_0^-1 with D = CCZ_012:
    T = [('TOFF', 0, 1, 2)]
    d = Derivation('T-CZ03-T', T + [('CZ', 0, 3)] + T, [('CCZ', 1, 2, 3), ('CZ', 0, 3)], L)
    # expand the Toffolis: a 3-wire window each
    d.win(0, 1, [('K', 0), ('CCZ', 0, 1, 2), ('Kd', 0)])
    d.win(4, 5, [('K', 0), ('CCZ', 0, 1, 2), ('Kd', 0)])
    # K_0^-1 CZ_03 K_0 = CX_30 (window {0,3})
    d.win(2, 5, [('CX', 3, 0)])
    # now K0 CCZ012 CX30 CCZ012 Kd0: the schema at target 0 needs the CCZ with its first wire 0 — it is
    d.win(1, 2, [('CCZ', 0, 1, 2)])          # (identity rewrite, keeps the spelling)
    # D CX30 D = CCZ123 CX30: from delta (CX30 CCZ012 CX30 = CCZ012 CCZ123) multiplied by D on the left and CX30 on the right
    # do it explicitly: insert CX30 CX30 = eps before D? Use the schema backward on nothing... We rewrite the window
    # [CCZ012, CX30, CCZ012] as [CX30, CCZ012, CX30, CCZ012] after inserting CX30 CX30 at the front:
    d.win(1, 1, [('CX', 3, 0), ('CX', 3, 0)])  # insert an involution pair (window on {0,3})
    d.delta(2)                                  # CX30 CCZ012 CX30 -> CCZ012 CCZ123
    # now K0 CX30 CCZ012 CCZ123 CCZ012 Kd0 ; CCZ123 commutes with CCZ012 (diagonals): 4 wires! — move CCZ123 right past CCZ012:
    # CCZ123 and CCZ012 share wires 1,2: delta backwards on [CCZ012, CCZ123]? that needs the pair order CCZ_buv CCZ_auv: b=0,a=3: CCZ012 CCZ312 -> CX30 CCZ012 CX30
    print('   at:', show(d.cur))
