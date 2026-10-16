# The gadgets of the affine decoding on four wires: circuits G₄(V) whose
# operator is the two-level V on the basis states 0 and e₀ (identity
# elsewhere), for V = iZ (phase pair), XZ (signed exchange) and K·i⁻¹
# with its pair reversed (the hybrid): joint/gad.py's G_pp, G_rot, G_ki
# (controls 1 2 3 black) conjugated by X on the wires 1 2 3.  Also the
# four-wire facts (F6) and the independence need, checked here
# numerically; each is one evaluation in Agda (Five/Gadgets, written here).
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
JD = os.path.join(os.path.dirname(HERE), 'joint')
sys.path.insert(0, HERE); sys.path.insert(0, JD)
import cs, gad
from derivn import flatten

N = 4
SEM = cs.Sem(N)
X3 = [('X', 1), ('X', 2), ('X', 3)]

def basic(word):
    """joint letters to generator tuples (iI, S w, K w, CS a b)."""
    return cs.to_generators(flatten(word))

def positive(word):
    out = []
    for g in basic(word):
        k = g[0]
        if k == 'Sd': out += [('S', g[1])] * 3
        elif k == 'CSd': out += adjacent_cs(*sorted(g[1:])) * 3
        elif k == 'iIi': out += [('iI',)] * 3
        elif k == 'Kd': out += [('K', g[1]), ('iI',)]
        elif k == 'CS': out += adjacent_cs(*sorted(g[1:]))
        else: out.append(g)
    return out

def _cx01(s): return [('K', s + 1), ('CS', s, s + 1), ('CS', s, s + 1), ('K', s + 1), ('iI',)]
def _cx10(s): return [('K', s), ('CS', s, s + 1), ('CS', s, s + 1), ('K', s), ('iI',)]
def _swap(s): return _cx01(s) + _cx10(s) + _cx01(s)

def adjacent_cs(a, b):
    """CS on wires a < b through adjacent gates: the swap of b-1, b around
    the CS of a, b-1."""
    if b == a + 1: return [('CS', a, b)]
    return _swap(b - 1) + adjacent_cs(a, b - 1) + _swap(b - 1)

def inv(word):
    """the inverse word over the generators: S⁻¹ = S³, CS⁻¹ = CS³, K⁻¹ = K i, i⁻¹ = i³."""
    out = []
    for g in reversed(word):
        k = g[0]
        if k == 'S': out += [g] * 3
        elif k == 'CS': out += [g] * 3
        elif k == 'iI': out += [g] * 3
        elif k == 'K': out += [g, ('iI',)]
        else: raise ValueError(g)
    return out

def eq(u, v): return SEM.eq(u, v)

S0 = [('S', 0)]
Sd0 = [('S', 0)] * 3
Z1 = [('S', 1), ('S', 1)]
CZ01 = [('CS', 0, 1), ('CS', 0, 1)]
CS01 = [('CS', 0, 1)]
CSd01 = [('CS', 0, 1)] * 3

G = {
    'pp':  positive(X3 + gad.G_pp(4) + X3),
    'rot': positive(X3 + gad.G_rot(4) + X3),
    'ki':  positive(X3 + gad.G_ki(4) + X3),
}
for k in list(G): G[k + '⁻'] = inv(G[k])

# The letters on the domain wires that the independence needs (wires 0..3):
# CX from wire j+1 onto j, and the SWAPs of the wires 1 2 and 2 3.
def cx10(s): return [('K', s), ('CS', s, s + 1), ('CS', s, s + 1), ('K', s), ('iI',)]
def cx01(s): return [('K', s + 1), ('CS', s, s + 1), ('CS', s, s + 1), ('K', s + 1), ('iI',)]
def swap(s): return cx01(s) + cx10(s) + cx01(s)
PASS = {'cx0': cx10(0), 'cx1': cx10(1), 'cx2': cx10(2), 'sw1': swap(1), 'sw2': swap(2)}

def commutes(a, b): return eq(a + b, b + a)


# (F6) through twisted commutators T(g) = g⁻¹ S⁻¹ g S (S on wire 0): with
# P, R, X the gadgets of iZ, XZ and the hybrid (orders 4, 4, 3),
#   P⁻ = T(R),  X⁻ = T(X⁻) P⁻,  R = X⁻ P X,
# found by scratch decsearch.py over the 24-element group.  Each is
# evaluated in a positive form, and Five/Gadgets turns it into the
# commutator form by group algebra:
#   (a) Sd R S P ≈ R,   (b) S P⁻ X X Sd ≈ X,   (c) X R ≈ P X.
# T(g) needs g to commute with S on wire 1 and CS on the wires 0 1, which
# every gadget does (it acts on 0 and e₀ alone); that is evaluated for R
# and X and carried to their inverses and products by algebra.
P_, R_, X_ = G['pp'], G['rot'], G['ki']
DEC = {
    'dec-a': (Sd0 + R_ + S0 + P_, R_, 'Sd • G-rot • S • G-pp', 'G-rot'),
    'dec-b': (S0 + G['pp⁻'] + X_ + X_ + Sd0, X_, 'S • G-pp ⁻¹ • G-ki • G-ki • Sd', 'G-ki'),
    'dec-c': (X_ + R_, P_ + X_, 'G-ki • G-rot', 'G-pp • G-ki'),
}
S1 = [('S', 1)]

def evaluations():
    """(name, lhs, rhs, agda lhs, agda rhs) for every evaluation."""
    out = []
    for k in ('pp', 'rot', 'ki'):
        a = NAMES[k]
        for (nm, L), (_, w) in zip(PASSAG, PASS.items()):
            out.append((f'{k}-{nm}', w + G[k], G[k] + w, f'({L}) • {a}', f'{a} • ({L})'))
    for k in ('rot', 'ki'):
        a = NAMES[k]
        out.append((f'{k}-s₁', S1 + G[k], G[k] + S1, f'S ↑ • {a}', f'{a} • S ↑'))
        out.append((f'{k}-cs', CS01 + G[k], G[k] + CS01, f'CS • {a}', f'{a} • CS'))
    for nm, (l, r, la, ra) in DEC.items():
        out.append((nm, l, r, la, ra))
    return out

def check():
    print({k: len(v) for k, v in G.items()})
    for nm, l, r, _, _ in evaluations():
        assert eq(l, r), nm
        print(nm, len(l) + len(r))
    print('all four-wire facts hold')

# ------------------------------------------------------------------ Agda
NAMES = {'pp': 'G-pp', 'rot': 'G-rot', 'ki': 'G-ki'}
PASSAG = [('cx₀', 'CX₁₀'), ('cx₁', 'CX₁₀ ↑'), ('cx₂', 'CX₁₀ ↑ ↑'), ('sw₁', 'Swap ↑'), ('sw₂', 'Swap ↑ ↑')]
BUDGET = 7000           # gates evaluated per module (about 1.9 GB of heap)
BANNER = '------------------------------------------------------------------------'
MOD = 'Examples.Groups.Clifford+CS.Five.Gadgets'

def gexpr(g):
    k = g[0]
    if k == 'iI': return 'iI'
    if k == 'CS':
        a, b = g[1], g[2]; assert b == a + 1, g
        return 'CS' + ' ↑' * a
    return k + ' ↑' * g[1]

def wexpr(word):
    es = [gexpr(g) for g in word]
    es = [f'({e})' if ' ' in e else e for e in es]
    return ' • '.join(es) if es else 'ε'

def words_module():
    out = [BANNER, '-- Presentations of groups', '--',
           '-- The gadgets of the affine decoding on four wires', '--',
           '-- G-pp, G-rot, G-ki act on the basis states 0 and e₀ as the two-level',
           '-- iZ, XZ and K·i⁻¹ (its pair exchanged), and as the identity elsewhere:',
           '-- the joint paper\'s G_pp, G_rot, G_ki (scratchpad/joint/gad.py) between',
           '-- X on the wires 1 2 3.  Written by `scratchpad/five/gadgets5.py`.',
           BANNER, '',
           '{-# OPTIONS --without-K --safe #-}', '',
           f'module {MOD}.Words where', '',
           'open import Word.Base using (_•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; S ; K ; CS ; iI ; _↑)', '',
           'Sd : Circuit 4', 'Sd = S • S • S', '']
    for k in ('pp', 'rot', 'ki'):
        out += [f'{NAMES[k]} : Circuit 4', f'{NAMES[k]} = {wexpr(G[k])}', '']
    return '\n'.join(out)

def eval_modules():
    """Pack the evaluations into modules of at most BUDGET gates."""
    mods, cur, size = [], [], 0
    for e in evaluations():
        n = len(e[1]) + len(e[2])
        if cur and size + n > BUDGET:
            mods.append(cur); cur, size = [], 0
        cur.append(e); size += n
    if cur: mods.append(cur)
    files = {}
    for i, es in enumerate(mods, 1):
        name = f'E{i:02d}'
        out = [BANNER, '-- Presentations of groups', '--',
               f'-- Four-wire facts about the gadgets ({", ".join(e[0] for e in es)})', '--',
               '-- Each is one evaluation, turned into a derivation by completeness on',
               '-- four wires; a module holds a few, since Agda frees the memory of an',
               '-- evaluation only when its module is done.  Written by',
               '-- `scratchpad/five/gadgets5.py`.',
               BANNER, '',
               '{-# OPTIONS --without-K --safe #-}', '',
               'open import Examples.Groups.Clifford+CS.Completeness using (Complete)', '',
               f'module {MOD}.{name} (c4 : Complete 4) where', '',
               'open import Relation.Binary.PropositionalEquality as Eq using ()',
               'open import Presentation.GroupLike using (module Group-Lemmas)',
               'open import Word.Base using (_•_)', '',
               'open import Examples.Groups.Clifford+CS.Syntactics',
               'open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)',
               f'open import {MOD}.Words', '',
               'open Group-Lemmas (_VRel,_===_ 4) grouplike using (_⁻¹)', '',
               'private', '  by : (u v : Circuit 4) → Same u v → 4 ⊢ u ≈ v', '  by u v e = c4 (same-sem u v e)', '']
        for nm, l, r, la, ra in es:
            out += [f'{nm} : 4 ⊢ {la} ≈ {ra}', f'{nm} = by ({la}) ({ra}) Eq.refl', '']
        files[name] = '\n'.join(out)
    return files

if __name__ == '__main__' and len(sys.argv) > 1:
    import io
    d = sys.argv[1]
    os.makedirs(d, exist_ok=True)
    io.open(os.path.join(d, 'Words.agda'), 'w', encoding='utf-8', newline='\n').write(words_module())
    for name, txt in eval_modules().items():
        io.open(os.path.join(d, name + '.agda'), 'w', encoding='utf-8', newline='\n').write(txt)
        print('written', name)

if __name__ == '__main__' and len(sys.argv) == 1:
    check()
