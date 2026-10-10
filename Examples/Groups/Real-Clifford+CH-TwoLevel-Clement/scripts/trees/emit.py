"""Emit the trees of trees.py as Agda terms (Tree.agda syntax)."""
import sys
sys.setrecursionlimit(50000)
from core import *
import trees

def zint(a): return '(+ %d)' % a if a >= 0 else '-[1+ %d ]' % (-a - 1)
def zz(x):
    return {(0, 0): '𝟎', (1, 0): '𝟏', (-1, 0): '-𝟏', (2, 0): '𝟐'}.get(x) or '(RootTwo %s %s)' % (zint(x[0]), zint(x[1]))
def fin(i):
    return 'f%d' % i
def vec(xs):
    return '(' + ' ∷ '.join(xs + ['[]']) + ')' if xs else '[]'
def lst(xs):
    return '(' + ' ∷ '.join(xs + ['[]']) + ')' if xs else '[]'
def form(f, vars_):
    return '(form %s %s)' % (zz(f.c), vec([zz(f.v.get(v, (0, 0))) for v in vars_]))
def boolean(b): return 'true' if b else 'false'

def letter(g, idx):
    if g[0] == 'H': return '(Hˡ %s %s)' % (fin(idx[g[1]]), fin(idx[g[2]]))
    if g[0] == 'X': return '(Xˡ %s %s)' % (fin(idx[g[1]]), fin(idx[g[2]]))
    return '(Zˡ %s)' % fin(idx[g[1]])

def emit(t, rows, vars_, out_defs, name):
    """the Agda term of tree t at a node with rows / vars; long subtrees become definitions"""
    idx = {r: i for i, r in enumerate(rows)}
    k = t[0]
    if k == 'leaf':
        c = t[1]
        con = 'l20' if c['core'] == '20' else 'l30'
        return '(leaf (%s %s %s %s))' % (con, vec([fin(idx[r]) for r in c['lab']]), lst([fin(idx[r]) for r in c['Q']]), boolean(c['flip']))
    if k == 'split':
        _, v, us, t0, t1 = t
        g = F(ZERO, {u: ONE for u in us})
        a = emit(t0, rows, vars_, out_defs, name + '0')
        b = emit(t1, rows, vars_, out_defs, name + '1')
        return '(split %s %s\n %s\n %s)' % (fin(vars_.index(v)), form(g, vars_), a, b)
    if k == 'extend':
        _, delta, kappa, route, cert, minp, row, v, sub = t
        kap = 'nothing' if kappa is None else '(just %s)' % boolean(kappa == 1)
        R = lst([letter(g, idx) for g in route])
        ce = ' '.join(fin(idx[r]) for r in cert)
        ps = lst(['(%s , %s)' % (fin(idx[a]), fin(idx[b])) for a, b in minp])
        s = emit(sub, [row] + rows, [v] + vars_, out_defs, name + 'e')
        return '(extend %d %s %s %s %s\n %s)' % (delta, kap, R, ce, ps, s)
    if k == 'conj':
        _, g, sub = t
        return '(conj %s\n %s)' % (letter(g, idx), emit(sub, rows, vars_, out_defs, name + 'c'))
    if k == 'relabel':
        _, newrows, sw, sub = t
        pi = vec([fin(idx[old]) for role, old in newrows])
        roles = [role for role, old in newrows]
        s = emit(sub, roles, vars_, out_defs, name + 'r')
        return '(relabel %s %s %s %s\n %s)' % (pi, boolean(sw), fin(roles.index('c')), fin(roles.index('d')), s)
    if k == 'reparam':
        _, nfname, tau, use = t
        nf = trees.NF38 if nfname == 'nf38' else trees.NF341
        assert rows == nf.roles, (rows, nf.roles)
        return '(useNF %s %s)' % (nfname, vec([form(tau[v], vars_) for v in nf.vars]))
    raise ValueError(k)

HEADER = """------------------------------------------------------------------------
-- Presentations of groups
--
-- %s
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.%s where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms using (Form ; form)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (Hˡ ; Xˡ ; Zˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree
"""

PRIV = """
private
  𝟎 𝟏 -𝟏 𝟐 : Z
  𝟎 = RootTwo (+ 0) (+ 0)
  𝟏 = RootTwo (+ 1) (+ 0)
  -𝟏 = RootTwo -[1+ 0 ] (+ 0)
  𝟐 = RootTwo (+ 2) (+ 0)
  f0 : ∀ {m} → Fin (suc m)
  f0 = zero
  f1 : ∀ {m} → Fin (suc (suc m))
  f1 = suc f0
  f2 : ∀ {m} → Fin (suc (suc (suc m)))
  f2 = suc f1
  f3 : ∀ {m} → Fin (suc (suc (suc (suc m))))
  f3 = suc f2
  f4 : ∀ {m} → Fin (suc (suc (suc (suc (suc m)))))
  f4 = suc f3
  f5 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc m))))))
  f5 = suc f4
  f6 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc m)))))))
  f6 = suc f5
  f7 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc m))))))))
  f7 = suc f6
  f8 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))
  f8 = suc f7
  f9 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))
  f9 = suc f8
  f10 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))
  f10 = suc f9
  f11 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))
  f11 = suc f10
  f12 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))
  f12 = suc f11
  f13 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))
  f13 = suc f12
  f14 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))
  f14 = suc f13
  f15 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))
  f15 = suc f14
  f16 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))))
  f16 = suc f15
  f17 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))))
  f17 = suc f16
  f18 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m)))))))))))))))))))
  f18 = suc f17
  f19 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc m))))))))))))))))))))
  f19 = suc f18
"""

