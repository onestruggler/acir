"""Generate Diagram20.agda and Diagram30.agda.

Clement's diagrams (20) and (30), read as relators Route = H[0,1], are
derived from his relations (20) and (21) on the first four and six
indices by explicit chains of steps (Chain: commuting letters, and
rewriting by a relation), each checked here; the chains are then
emitted as `derive` proofs for Real-Clifford+CH-TwoLevel.Engine.

Usage: python gen.py [OUTDIR]   (default: the development's folder)
"""
import os, sys
from deriv import *
from words import *
from manual import Chain
from emit import *
from routes import CORES

OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')

def pair_name(g):
    if g[0] == 'Z':
        return 'a1-%d' % g[1]
    if g[0] == 'X':
        return 'a2-%d%d' % (g[1], g[2])
    return 'a3-%d%d' % (g[1], g[2])

class D6(Deriver):
    def pair_name(self, g):
        return pair_name(g)

def diagram(m, Lname, Lw, Rw, conjugator, hypname):
    """route = Lcol + C0 + rev(Lcol) as an operator word; conjugator P' with
    C0 P' ~ P' C0 the hypothesis (L = C0 + P', R = P' + C0)."""
    D = D6(m)
    D.add_eq(hypname, Lw, Rw, both=True)
    return D

DERIVS = {}

# ---- (30) from (21)
L30col = [H(0, 2), H(1, 3), H(0, 4), H(1, 5), H(0, 1), Z(0), Z(1), H(1, 5), H(0, 4), H(1, 3), H(0, 2)]
route30 = CORES['30'][0]
assert route30 == L30col + C0 + list(reversed(L30col)), (route30,)
Pp = A1 + A2 + C0 + S0 + A2 + A1
D = D6(6)
D.add_eq('r21e', L21, R21, both=True)
ch = Chain(D, route30)
# the suffix rev(L30col) = [H02,H13,H04,H15,Z1,Z0,H01,H15,H04,H13,H02] becomes P'
base = len(L30col) + 1
cur = list(ch.cur)
cur[base + 4], cur[base + 5] = cur[base + 5], cur[base + 4]          # Z1 Z0 -> Z0 Z1
ch.perm(cur)
ch.rw('d1-01', base + 4)                                             # Z0 Z1 H01 -> H01 Z0 Z1
cur = list(ch.cur)
cur[base + 7:base + 11] = [H(0, 4), H(1, 5), H(0, 2), H(1, 3)]
ch.perm(cur)
assert ch.cur[base:] == Pp
ch.rw('r21e', base - 1)                                              # C0 P' -> P' C0
# the prefix L30col: H01 Z0 Z1 -> Z0 Z1 H01, then everything before the final C0 cancels
ch.rw('(sym⁼ d1-01)', 4)
ch.cancel()
ch.finish('d30', C0)
DERIVS['30'] = D.derived

# ---- (20) from (20)
L20col = [H(0, 2), H(1, 3), H(0, 1), Z(0), Z(1), H(1, 3), H(0, 2)]
route20 = CORES['20'][0]
assert route20 == L20col + C0 + list(reversed(L20col)), (route20,)
Q = A + C0 + S0 + A
assert L20 == C0 + Q and R20 == Q + C0
D4 = D6(4)
D4.add_eq('r20e', L20, R20, both=True)
ch = Chain(D4, route20)
base = len(L20col) + 1
cur = list(ch.cur)
cur[base + 2], cur[base + 3] = cur[base + 3], cur[base + 2]
ch.perm(cur)
ch.rw('d1-01', base + 2)
cur = list(ch.cur)
cur[base + 5:base + 7] = [H(0, 2), H(1, 3)]
ch.perm(cur)
assert ch.cur[base:] == Q, ch.cur[base:]
ch.rw('r20e', base - 1)
ch.rw('(sym⁼ d1-01)', 2)
ch.cancel()
ch.finish('d20', C0)
DERIVS['20'] = D4.derived


# ---- emission

def module(m, name, doc, hyp, hypL, hypR, derivs, dname, route):
    lists = [(hypL[0], hypL[1]), (hypR[0], hypR[1]), ('Route', route), ('C0w', C0)]
    used = collect(derivs)
    for _, w in lists: used |= set(w)
    out = []
    w = out.append
    w('------------------------------------------------------------------------')
    w('-- Presentations of groups')
    w('--')
    for line in doc: w('-- ' + line if line else '--')
    w('------------------------------------------------------------------------')
    w('')
    w('{-# OPTIONS --without-K --safe #-}')
    w('')
    w('open import Word.Base using (WRel)')
    w('import Presentation.Base as PB')
    w('open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)')
    w('open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)')
    w('')
    w('module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.%s where' % name)
    w('')
    w('open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)')
    w('open import Data.List.Base using (List ; [] ; _∷_)')
    w('open import Data.Nat.Base using (z≤n ; s≤s)')
    w('open import Relation.Binary.PropositionalEquality using (refl)')
    w('')
    w('open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (H-gen ; X-gen ; Z-gen)')
    w('import Presentation.Tactics.Words as TW')
    w('')
    w('------------------------------------------------------------------------')
    w('-- Letters')
    w('')
    for line in letters_block(m, used): w(line)
    w('')
    w('------------------------------------------------------------------------')
    w('-- The relation and the diagram as letter lists (operator order)')
    w('')
    for nm, lst in lists:
        w('%s : List (Gen %d)' % (nm, m))
        w('%s = %s' % (nm, alist(lst)))
    w('')
    w('------------------------------------------------------------------------')
    w('-- The diagram commutes')
    w('')
    sec = section('From', [(hyp, hypL[0], hypR[0])], derivs, [(dname, dname, 'Route', 'C0w')])
    # the module header: parameters Γ, loc and the hypothesis (word-of-list spelled out)
    sec[0] = ('module From (Γ : WRel (Gen %d)) (loc : ∀ {u v} → u ===ˡ v → PB._≈_ Γ u v)' % m
              + chr(10) +
              '  (%sh : PB._≈_ Γ (TW.Associative.word-of-list %s) (TW.Associative.word-of-list %s)) where' % (hyp, hypL[0], hypR[0]))
    sec.insert(1, '')
    sec.insert(2, '  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Engine Γ loc')
    sec.insert(3, '  open PB Γ using (_≈_)')
    out += sec
    path = os.path.join(OUT, name + '.agda')
    open(path, 'w', encoding='utf-8').write('\n'.join(out) + '\n')
    print('written', name)

module(6, 'Diagram30', [
    "On six indices, in any set of relations Γ that derives the local",
    "ones: Clément's (21) gives his diagram (30) (Lemma 3.17), read as the",
    "relation Route = H_[0,1] where Route goes down its left side, along",
    "the bottom H_[0,1] and up its right side.  Its sides are the word P of",
    "(21), C₀ P = P C₀, up to commuting letters and (d1).",
], 'r21e', ('L21', L21), ('R21', R21), DERIVS['30'], 'd30', CORES['30'][0])

module(4, 'Diagram20', [
    "On four indices, in any set of relations Γ that derives the local",
    "ones: Clément's (20) gives the diagram of his Subcase 3.4.1, read as",
    "the relation Route = H_[0,1] (as for Diagram30).",
], 'r20e', ('L20', L20), ('R20', R20), DERIVS['20'], 'd20', CORES['20'][0])
