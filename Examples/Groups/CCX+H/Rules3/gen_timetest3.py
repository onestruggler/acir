"""Write TimeTest3.agda: equalities decided by row actions on a scaled integer matrix."""
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


PERMS = {'tX0': flip(0), 'tX1': flip(1), 'tX2': flip(2), 'tCX0': flip(0, (1,)),
         'tCX1': flip(1, (2,)), 'tSW0': swap(0, 1), 'tSW1': swap(1, 2), 'tCCX0': flip(0, (1, 2))}
pat = ' ∷ '.join(f'r{i}' for i in range(8)) + ' ∷ []'
out = ['{-# OPTIONS --without-K --safe #-}',
       'module Examples.Groups.CCX+H.Rules3.TimeTest3 where',
       'open import Data.Bool.Base using (Bool ; true ; false ; _∧_)',
       'open import Data.Integer.Base using (ℤ ; +_ ; -[1+_] ; _+_ ; _-_ ; _*_)',
       'import Data.Integer.Properties as ℤP',
       'open import Data.List.Base using (List ; [] ; _∷_ ; _++_)',
       'open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)',
       'open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map ; zipWith ; foldr)',
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
       '_⊕_ _⊖_ : Row → Row → Row',
       'u ⊕ v = zipWith _+_ u v',
       'u ⊖ v = zipWith _-_ u v',
       '',
       '-- (a, b, c, d) ↦ H ⊗ H, unscaled: (a+b+c+d, a-b+c-d, a+b-c-d, a-b-c+d)',
       'h4 : Row → Row → Row → Row → Vec Row 4',
       'h4 a b c d = ((a ⊕ b) ⊕ (c ⊕ d)) ∷ ((a ⊖ b) ⊕ (c ⊖ d)) ∷ ((a ⊕ b) ⊖ (c ⊕ d)) ∷ ((a ⊖ b) ⊖ (c ⊖ d)) ∷ []',
       '',
       'act : Tok → Mat → Mat']
for name, f in PERMS.items():
    # new row i = old row f^-1(i): (T M)[i] = M[j] where f(j) = i
    inv = {f(j): j for j in range(8)}
    rhs = ' ∷ '.join(f'r{inv[i]}' for i in range(8)) + ' ∷ []'
    out.append(f'act {name} ({pat}) = {rhs}')
# HH0: wires 0,1: blocks {0,1,2,3} and {4,5,6,7}; index within block = b0 + 2 b1
out.append(f'act tHH0 ({pat}) with h4 r0 r1 r2 r3 | h4 r4 r5 r6 r7')
out.append('... | s0 ∷ s1 ∷ s2 ∷ s3 ∷ [] | s4 ∷ s5 ∷ s6 ∷ s7 ∷ [] = s0 ∷ s1 ∷ s2 ∷ s3 ∷ s4 ∷ s5 ∷ s6 ∷ s7 ∷ []')
# HH1: wires 1,2: blocks {0,2,4,6} and {1,3,5,7}
out.append(f'act tHH1 ({pat}) with h4 r0 r2 r4 r6 | h4 r1 r3 r5 r7')
out.append('... | s0 ∷ s2 ∷ s4 ∷ s6 ∷ [] | s1 ∷ s3 ∷ s5 ∷ s7 ∷ [] = s0 ∷ s1 ∷ s2 ∷ s3 ∷ s4 ∷ s5 ∷ s6 ∷ s7 ∷ []')
out += ['',
        'hs : Tok → ℕ',
        'hs tHH0 = 1',
        'hs tHH1 = 1',
        'hs _ = 0',
        '',
        'toL : Word Tok → List Tok',
        'toL [ t ]ʷ = t ∷ []',
        'toL ε = []',
        'toL (u • v) = toL u ++ toL v',
        '',
        'I8 : Mat',
        'I8 = ' + ' ∷ '.join('(' + ' ∷ '.join('+ 1' if i == j else '+ 0' for j in range(8)) + ' ∷ [])' for i in range(8)) + ' ∷ []',
        '',
        'run : List Tok → ℕ → Mat → ℕ × Mat',
        'run [] k m = k , m',
        'run (t ∷ ts) k m = run ts (hs t ℕ.+ k) (act t m)',
        '',
        'eqZ : ℤ → ℤ → Bool',
        'eqZ x y = does (x ℤP.≟ y)',
        '',
        'pow2 : ℕ → ℤ',
        'pow2 zero = + 1',
        'pow2 (suc n) = + 2 * pow2 n',
        '',
        'eqM : ℕ × Mat → ℕ × Mat → Bool',
        'eqM (k , a) (l , b) = foldr _ _∧_ true (zipWith (λ u v → foldr _ _∧_ true (zipWith eqZ u v)) (map (map (pow2 l *_)) a) (map (map (pow2 k *_)) b))',
        '',
        '-- the matrix of t1 ... tn is T1 (T2 (... (Tn I))): run the reversed list',
        'rev : List Tok → List Tok',
        'rev [] = []',
        'rev (t ∷ ts) = rev ts ++ (t ∷ [])',
        '',
        'chk : Word Tok → Word Tok → Bool',
        'chk u v = eqM (run (rev (toL u)) 0 I8) (run (rev (toL v)) 0 I8)',
        '']
out.insert(4, 'open import Data.Product.Base using (_×_ ; _,_)')
for i, (w, v) in enumerate(pairs):
    out.append(f'u{i} v{i} : Word Tok')
    out.append(f'u{i} = {ag(w)}')
    out.append(f'v{i} = {ag(v)}')
out.append('ok : ' + ' ∧ '.join(f'chk u{i} v{i}' for i in range(N)) + ' ≡ true')
out.append('ok = refl')
open('TimeTest3.agda', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
