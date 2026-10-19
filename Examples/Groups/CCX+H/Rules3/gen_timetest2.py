"""Write TimeTest2.agda: the same equalities decided on scaled integer matrices."""
import random, sys
from syn import M, theta_word, THETA_T

rng = random.Random(5)
L = int(sys.argv[1]) if len(sys.argv) > 1 else 100
N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
pairs = []
for _ in range(N):
    w = tuple(rng.choice(THETA_T) for _ in range(L))
    v = theta_word(M(w))
    pairs.append((w, v))

TOK = {'X0': 'tX0', 'X1': 'tX1', 'X2': 'tX2', 'CX0': 'tCX0', 'CX1': 'tCX1',
       'HH0': 'tHH0', 'HH1': 'tHH1', 'SW0': 'tSW0', 'SW1': 'tSW1', 'CCX0': 'tCCX0'}


def ag(w):
    if not w:
        return 'ε'
    return ' • '.join('[ ' + TOK[t] + ' ]ʷ' for t in w)


# token matrices: rows of the integer matrix, index l = x0 + 2 x1 + 4 x2
def perm_rows(f):
    rows = []
    for i in range(8):
        rows.append([1 if f(j) == i else 0 for j in range(8)])
    return rows


def bit(x, k):
    return x >> k & 1


def flip(t, ctrls=()):
    return lambda j: j ^ (1 << t) if all(bit(j, c) for c in ctrls) else j


def swap(a, b):
    def f(j):
        if bit(j, a) != bit(j, b):
            return j ^ (1 << a) ^ (1 << b)
        return j
    return f


def hh_rows(a, b):
    rows = []
    for i in range(8):
        r = []
        for j in range(8):
            same = all(bit(i, k) == bit(j, k) for k in range(3) if k not in (a, b))
            if not same:
                r.append(0)
            else:
                s = bit(i, a) * bit(j, a) + bit(i, b) * bit(j, b)
                r.append(-1 if s % 2 else 1)
        rows.append(r)
    return rows


MATS = {'tX0': (0, perm_rows(flip(0))), 'tX1': (0, perm_rows(flip(1))), 'tX2': (0, perm_rows(flip(2))),
        'tCX0': (0, perm_rows(flip(0, (1,)))), 'tCX1': (0, perm_rows(flip(1, (2,)))),
        'tSW0': (0, perm_rows(swap(0, 1))), 'tSW1': (0, perm_rows(swap(1, 2))),
        'tCCX0': (0, perm_rows(flip(0, (1, 2)))),
        'tHH0': (1, hh_rows(0, 1)), 'tHH1': (1, hh_rows(1, 2))}


def zi(x):
    return f'+ {x}' if x >= 0 else f'-[1+ {-x - 1} ]'


out = ['{-# OPTIONS --without-K --safe #-}',
       'module Examples.Groups.CCX+H.Rules3.TimeTest2 where',
       'open import Data.Bool.Base using (Bool ; true ; false ; _∧_)',
       'open import Data.Integer.Base using (ℤ ; +_ ; -[1+_] ; _+_ ; _*_)',
       'import Data.Integer.Properties as ℤP',
       'open import Data.Nat.Base using (ℕ ; zero ; suc)',
       'open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map ; zipWith ; foldr ; replicate ; transpose)',
       'open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)',
       'open import Relation.Nullary.Decidable using (does)',
       'open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)',
       '',
       'data Tok : Set where',
       '  ' + ' '.join(TOK.values()) + ' : Tok',
       '',
       'Row = Vec ℤ 8',
       'Mat = Vec Row 8',
       '',
       'record SM : Set where',
       '  constructor sm',
       '  field k : ℕ ; m : Mat',
       '',
       'dot : Row → Row → ℤ',
       'dot u v = foldr _ _+_ (+ 0) (zipWith _*_ u v)',
       '',
       'mmul : Mat → Mat → Mat',
       'mmul a b = map (λ r → map (dot r) (transpose b)) a',
       '',
       'smul : SM → SM → SM',
       'smul (sm k a) (sm l b) = sm (k Data.Nat.Base.+ l) (mmul a b)',
       '  where import Data.Nat.Base',
       '',
       'tok : Tok → SM']
for name, (k, rows) in MATS.items():
    rs = ' ∷ '.join('(' + ' ∷ '.join('(' + zi(x) + ')' for x in r) + ' ∷ [])' for r in rows) + ' ∷ []'
    out.append(f'tok {name} = sm {k} ({rs})')
out += ['',
        'I8 : SM',
        'I8 = sm 0 (' + ' ∷ '.join('(' + ' ∷ '.join('(+ 1)' if i == j else '(+ 0)' for j in range(8)) + ' ∷ [])' for i in range(8)) + ' ∷ [])',
        '',
        'fast : Word Tok → SM',
        'fast [ t ]ʷ = tok t',
        'fast ε = I8',
        'fast (u • v) = smul (fast u) (fast v)',
        '',
        'pow2 : ℕ → ℤ',
        'pow2 zero = + 1',
        'pow2 (suc n) = + 2 * pow2 n',
        '',
        'eqZ : ℤ → ℤ → Bool',
        'eqZ x y = does (x ℤP.≟ y)',
        '',
        'eqRow : Row → Row → Bool',
        'eqRow u v = foldr _ _∧_ true (zipWith eqZ u v)',
        '',
        'scale : ℤ → Mat → Mat',
        'scale c = map (map (c *_))',
        '',
        'eqSM : SM → SM → Bool',
        'eqSM (sm k a) (sm l b) = foldr _ _∧_ true (zipWith eqRow (scale (pow2 l) a) (scale (pow2 k) b))',
        '',
        'chk : Word Tok → Word Tok → Bool',
        'chk u v = eqSM (fast u) (fast v)',
        '']
for i, (w, v) in enumerate(pairs):
    out.append(f'u{i} v{i} : Word Tok')
    out.append(f'u{i} = {ag(w)}')
    out.append(f'v{i} = {ag(v)}')
out.append('ok : ' + ' ∧ '.join(f'chk u{i} v{i}' for i in range(N)) + ' ≡ true')
out.append('ok = refl')
open('TimeTest2.agda', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
