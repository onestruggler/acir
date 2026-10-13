"""Knuth-Bendix completion for one qutrit, with derivations, and the
Agda module deriving BoxRelations₁ from C₁-C₅.

Words are tuples over 'n' (the scalar -ω), 'h', 's' (H and S on wire 0),
in operator order (Agda's list order).  Every equation ever created is a
lemma; a derivation is a list of steps (pos, eq id, dir) rewriting the
current word at pos with that equation, left to right (dir +1) or right
to left (dir -1)."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import re, sys
from pauli_act import ev, defs as NFdefs

ORDER = {'n': 0, 'h': 1, 's': 2}
def key(w):
    return (len(w), [ORDER[c] for c in w])

EQS = {}          # id -> dict(l, r, name, steps)
ACTIVE = []       # list of (id, dir): rules src -> dst
NEXT = [0]

def new_eq(l, r, steps=None, name=None):
    i = NEXT[0]; NEXT[0] += 1
    EQS[i] = dict(l=tuple(l), r=tuple(r), name=name, steps=steps)
    return i

def src(rule):
    i, d = rule; e = EQS[i]
    return e['l'] if d > 0 else e['r']
def dst(rule):
    i, d = rule; e = EQS[i]
    return e['r'] if d > 0 else e['l']

def apply(w, pos, i, d):
    e = EQS[i]
    a, b = (e['l'], e['r']) if d > 0 else (e['r'], e['l'])
    assert w[pos:pos + len(a)] == a, (w, pos, i, d)
    return w[:pos] + b + w[pos + len(a):]

def find(w):
    for p in range(len(w)):
        for rule in ACTIVE:
            s = src(rule)
            if w[p:p + len(s)] == s:
                return p, rule
    return None

def normalise(w):
    steps = []
    while True:
        f = find(w)
        if f is None: return w, steps
        p, (i, d) = f
        w = apply(w, p, i, d)
        steps.append((p, i, d))

def reverse(steps):
    return [(p, i, -d) for (p, i, d) in reversed(steps)]

def check_path(a, steps, b):
    w = a
    for p, i, d in steps:
        w = apply(w, p, i, d)
    assert w == b, (a, b, w)

# axioms, as in Axioms.agda, and the commutations of the scalar
ax = {}
ax['C1'] = new_eq('nnnnnn', '', name='C₁ᵉ')
ax['C2'] = new_eq('hhhh', '', name='C₂ᵉ')
ax['C3'] = new_eq('sss', '', name='C₃ᵉ')
ax['C4'] = new_eq('hsshsshss', 'n', name='C₄ᵉ')
ax['C5'] = new_eq('hhshhs', 'shhshh', name='C₅ᵉ')
ax['hn'] = new_eq('hn', 'nh', name='comm-h')
ax['sn'] = new_eq('sn', 'ns', name='comm-s')

PENDING = []
for i in ax.values():
    PENDING.append((EQS[i]['l'], EQS[i]['r'], [(0, i, 1)]))

def add_pair(a, b, path):
    """a ->path-> b; normalise both and orient."""
    na, sa = normalise(a)
    nb, sb = normalise(b)
    if na == nb: return
    full = reverse(sa) + path + sb          # na -> nb
    check_path(na, full, nb)
    if key(na) > key(nb):
        l, r, st = na, nb, full
    else:
        l, r, st = nb, na, reverse(full)
    i = new_eq(l, r, steps=st)
    rule = (i, 1)
    # interreduce
    keep = []
    for old in ACTIVE:
        s = src(old)
        if any(s[p:p + len(l)] == l for p in range(len(s))):
            PENDING.append((src(old), dst(old), [(0, old[0], old[1])]))
        else:
            keep.append(old)
    ACTIVE[:] = keep
    ACTIVE.append(rule)

def critical_pairs(r1, r2):
    l1, l2 = src(r1), src(r2)
    out = []
    for k in range(1, min(len(l1), len(l2))):
        if l1[-k:] == l2[:k]:
            w = l1 + l2[k:]
            a = apply(w, 0, *r1)
            b = apply(w, len(l1) - k, *r2)
            out.append((a, [(0, r1[0], -r1[1]), (len(l1) - k, r2[0], r2[1])], b))
    for p in range(len(l1) - len(l2) + 1):
        if l1[p:p + len(l2)] == l2 and r1 != r2:
            a = apply(l1, 0, *r1)
            b = apply(l1, p, *r2)
            out.append((a, [(0, r1[0], -r1[1]), (p, r2[0], r2[1])], b))
    return out

def complete(limit=5000):
    done = set()
    while True:
        while PENDING:
            a, b, path = PENDING.pop(0)
            add_pair(a, b, path)
        new = False
        for r1 in list(ACTIVE):
            for r2 in list(ACTIVE):
                if (r1, r2) in done: continue
                done.add((r1, r2))
                if r1 not in ACTIVE or r2 not in ACTIVE: continue
                for a, path, b in critical_pairs(r1, r2):
                    PENDING.append((a, b, path))
                    new = True
                while PENDING:
                    a, b, path = PENDING.pop(0)
                    add_pair(a, b, path)
        if not new: break
        if len(ACTIVE) > limit: raise Exception('too many rules')

complete()
print('active rules', len(ACTIVE), 'equations', len(EQS), file=sys.stderr)

# ---------------------------------------------------------------- the boxes
CH = {('H', 0): 'h', ('S', 0): 's', ('nu',): 'n'}
def word(lst):
    return ''.join(CH[t] for t in lst)
def box(k, ix):
    return word(ev(NFdefs['%sl %s%s' % (k, k, ''.join('₀₁₂'[i] for i in ix))]))
X = word(ev(NFdefs['Xˡ'])); Zw = word(ev(NFdefs['Zˡ']))
W0 = {'iS': 's', 'iX': X, 'iZ': Zw, 'iν': 'n'}
CO = {'coS': 's', 'coZ': Zw, 'coν': 'n'}
HS = {'gH': 'h', 'gS': 's'}
SUB = '₀₁₂'
def idx(name):          # A₁₂ -> (1, 2)
    return tuple(SUB.index(c) for c in name[1:])

tables = open(ROOT + '/Tables.agda', encoding='utf-8').read()
def toks(lst):
    lst = lst.strip()
    if lst == '[]': return []
    parts = [t.strip() for t in lst.split('∷')]
    assert parts[-1] == '[]', lst
    return parts[:-1]

BOX = []   # (agda clause head, field, lhs word, rhs word)
for m in re.finditer(r'^ruleA (A\S+) (g\S) = (A\S+) , (.*)$', tables, re.M):
    a, h, a2, lst = m.groups()
    BOX.append(('ruleA', (a, h), box('A', idx(a)) + HS[h],
                ''.join(W0[t] for t in toks(lst)) + box('A', idx(a2))))
for m in re.finditer(r'^ruleC (C\S+) (i\S) = (C\S+) , (.*)$', tables, re.M):
    c, g, c2, lst = m.groups()
    BOX.append(('ruleC', (c, g), box('C', idx(c)) + W0[g],
                ''.join(CO[t] for t in toks(lst)) + box('C', idx(c2))))
for m in re.finditer(r'^ruleE (E\S+) = (E\S+)$', tables, re.M):
    e, e2 = m.groups()
    BOX.append(('ruleE', (e,), box('E', idx(e)) + 's', box('E', idx(e2))))
for m in re.finditer(r'^ruleE (E\S+) = (E\S+)$', tables, re.M):
    e, _ = m.groups()
    BOX.append(('ruleEZ', (e,), box('E', idx(e)) + Zw, Zw + box('E', idx(e))))
for m in re.finditer(r'^ruleF (F\S+) = (F\S+)$', tables, re.M):
    f, f2 = m.groups()
    BOX.append(('ruleF', (f,), box('F', idx(f)) + Zw, box('F', idx(f2))))
print('box relations', len(BOX), file=sys.stderr)

PROOFS = []
for fam, args, l, r in BOX:
    nl, sl = normalise(tuple(l)); nr, sr = normalise(tuple(r))
    assert nl == nr, (fam, args, l, r, nl, nr)
    st = sl + reverse(sr)
    check_path(tuple(l), st, tuple(r))
    PROOFS.append((fam, args, l, r, st))

# the lemmas needed
need = set()
stack = [i for (_, _, _, _, st) in PROOFS for (_, i, _) in st]
while stack:
    i = stack.pop()
    if i in need: continue
    need.add(i)
    if EQS[i]['steps']:
        stack += [j for (_, j, _) in EQS[i]['steps']]
print('lemmas needed', len([i for i in need if EQS[i]['name'] is None]), file=sys.stderr)

AG = {'n': '𝕟', 'h': 'h₀', 's': 's₀'}
def alist(w):
    return ' ∷ '.join([AG[c] for c in w] + ['[]'])
def ename(i, d):
    e = EQS[i]
    nm = e['name'] or 'L%d' % i
    return nm if d > 0 else '(sym⁼ %s)' % nm
def asteps(st):
    return ' ∷ '.join(['rw %d %s' % (p, ename(i, d)) for (p, i, d) in st] + ['[]'])

out = []
w = out.append
w('''------------------------------------------------------------------------
-- Presentations of groups
--
-- The box relations on one qutrit (Appendix C.2), derived from C₁–C₅
--
-- A Knuth–Bendix completion of C₁–C₅ (with the scalar commuting with
-- H and S) for the shortlex order −ω < H < S; every rule it creates is
-- a lemma below, derived from earlier ones by rewriting, and each box
-- relation rewrites both of its sides to the same normal form.  Only
-- the lemmas the box relations use are kept.  Generated by
-- scratchpad qt/kb_one.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Box1 where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Notations using (₁₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (Eqn ; prf ; sym⁼ ; derive ; perm ; rw ; ⟪_⟫)
open import Examples.Groups.Qutrit-Clifford.Axioms
open import Examples.Groups.Qutrit-Clifford.NormalForm
open import Examples.Groups.Qutrit-Clifford.Tables

private
  variable
    n : ℕ

-- The scalar commutes with H and S.
comm-h comm-s : Eqn (₁₊ n)
comm-h = derive (h₀ ∷ 𝕟 ∷ []) (𝕟 ∷ h₀ ∷ []) (perm (𝕟 ∷ h₀ ∷ []) ∷ []) refl
comm-s = derive (s₀ ∷ 𝕟 ∷ []) (𝕟 ∷ s₀ ∷ []) (perm (𝕟 ∷ s₀ ∷ []) ∷ []) refl

------------------------------------------------------------------------
-- The completion

''')
for i in sorted(need):
    e = EQS[i]
    if e['name'] is not None: continue
    w('L%d : Eqn (₁₊ n)\nL%d = derive (%s)\n  (%s)\n  (%s) refl\n\n'
      % (i, i, alist(e['l']), alist(e['r']), asteps(e['steps'])))

w('''------------------------------------------------------------------------
-- The box relations

''')
names = {}
for fam, args, l, r, st in PROOFS:
    nm = 'b-%s-%s' % (fam, '-'.join(args))
    names[(fam, args)] = nm
    w('%s : Eqn (₁₊ n)\n%s = derive (%s)\n  (%s)\n  (%s) refl\n\n'
      % (nm, nm, alist(l), alist(r), asteps(st)))

def clauses(fam, fld, ty):
    w('  %s : %s\n' % (fld, ty))
    for (f, args), nm in names.items():
        if f == fam:
            w('  %s %s = prf %s\n' % (fld, ' '.join(args), nm))

w('''br₁ : BoxRelations₁
br₁ = record
  { ruleA-ok = A-ok ; ruleC-ok = C-ok ; ruleE-ok = E-ok ; ruleEZ-ok = EZ-ok ; ruleF-ok = F-ok }
  where
''')
clauses('ruleA', 'A-ok', '∀ {n} (a : AT) (h : HS) →\n    (₁₊ n) ⊢ ⟪ Al a ++ HSl h ⟫ ≈ ⟪ W0ls (proj₂ (ruleA a h)) ++ Al (proj₁ (ruleA a h)) ⟫')
clauses('ruleC', 'C-ok', '∀ {n} (c : CT) (g : W0) →\n    (₁₊ n) ⊢ ⟪ Cl c ++ W0l g ⟫ ≈ ⟪ COls (proj₂ (ruleC c g)) ++ Cl (proj₁ (ruleC c g)) ⟫')
clauses('ruleE', 'E-ok', '∀ {n} (e : ET) → (₁₊ n) ⊢ ⟪ El e ++ s₀ ∷ [] ⟫ ≈ ⟪ El (ruleE e) ⟫')
clauses('ruleEZ', 'EZ-ok', '∀ {n} (e : ET) → (₁₊ n) ⊢ ⟪ El e ++ Zˡ ⟫ ≈ ⟪ Zˡ ++ El e ⟫')
clauses('ruleF', 'F-ok', '∀ {n} (f : FT) → (₁₊ n) ⊢ ⟪ Fl f ++ Zˡ ⟫ ≈ ⟪ Fl (ruleF f) ⟫')

open(ROOT + '/Box1.agda', 'w', encoding='utf-8', newline='\n').write(''.join(out))
print('written', file=sys.stderr)
