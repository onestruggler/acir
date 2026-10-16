# The five-wire window lemmas of (F6), the gadget commuting with CX from
# wire 1 onto wire 4 (Five/F6): with A = CX(1→4), C = λ⁰(S₀) = X4 CS04 X4
# and E = CS01⁻¹ CCZ014,
#   cx14 : A = K4 CS14 CS14 K4 i        (A is K4 λ¹(Z₁) K4, up to the scalar)
#   w1   : A C A = E C
#   w2   : A C³ A = C³ CS01 CCZ014      (= C³ E⁻¹)
#   aa   : A A = ε
#   ee   : CS01 CCZ014 CS01⁻¹ CCZ014 = ε
# each one window; and the joint lemma SB2, Σ01 Σ01 = CCZ014.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lower5 as L5
from prim5 import Prim

A = ('CX', 1, 4)
X4 = ('X', 4)
CS04 = ('CS', 0, 4)
C = [X4, CS04, X4]
CCZ = ('CCZ', 0, 1, 4)

OBL = {
    'f6 cx14': ([A], [('K', 4), ('CS', 1, 4), ('CS', 1, 4), ('K', 4), ('iI', 0)]),
    'f6 w1': ([A] + C + [A], [('CSd', 0, 1), CCZ] + C),
    'f6 w2': ([A] + C * 3 + [A], C * 3 + [('CS', 0, 1), CCZ]),
    'f6 aa': ([A, A], []),
    'f6 ee': ([('CS', 0, 1), CCZ, ('CSd', 0, 1), CCZ], []),
    # the letters touching wire 4 for the independence
    'f6 cx43': ([('CX', 4, 3)], [('CK', 4, 3), ('CS', 3, 4), ('CS', 3, 4), ('CK', 4, 3), ('S', 4)]),
    'f6 cx34': ([('CX', 3, 4)], [('SWAP', 2, 3), ('SWAP', 1, 2), A, ('SWAP', 1, 2), ('SWAP', 2, 3)]),
    'f6 sw34': ([('SWAP', 3, 4)], [('CX', 3, 4), ('CX', 4, 3), ('CX', 3, 4)]),
}

def all_obligations():
    out = {}
    for name, (l, r) in OBL.items():
        if name not in L5.LEMMAS:
            P = Prim(name, l, r, L5.LEMMAS)
            L5.lower_window(P, 0, len(l), r)
            P.done(); L5.PRIMS.append(P)
        out[name] = name
    out['sb2'] = L5.instance('SB2', {})
    return out

def lst(letters, mname):
    return '(' + ' ∷ '.join(mname(g) for g in letters) + ' ∷ [])' if letters else '[]'

def agda_module(res, modof, lemname, mname, MOD):
    deps = {}
    def use(name):
        deps.setdefault(modof[name], set()).add(lemname(name)); return f'{lemname(name)} c4'
    NL = chr(10)
    defs = []
    for key, name in (('cx14', 'f6 cx14'), ('w1', 'f6 w1'), ('w2', 'f6 w2'), ('aa', 'f6 aa'), ('ee', 'f6 ee'),
                      ('cx43', 'f6 cx43'), ('cx34', 'f6 cx34'), ('sw34', 'f6 sw34'), ('sb2', res['sb2'])):
        l, r = L5.LEMMAS[name]
        defs.append(f'{key} : Complete 4 → ⟪ {lst(l, mname)} ⟫ʷ ≈ ⟪ {lst(r, mname)} ⟫ʷ')
        defs.append(f'{key} c4 = {use(name)}')
        defs.append('')
    dep_lines = NL.join(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(ns))})' for m, ns in sorted(deps.items()))
    return f"""------------------------------------------------------------------------
-- Presentations of groups
--
-- The five-wire window lemmas of (F6)
--
-- With A = CX(1→4), C = λ⁰(S₀) = X4 CS04 X4 and E = CS01⁻¹ CCZ014:
-- A = K4 CS14 CS14 K4 i, A C A = E C, A C³ A = C³ CS01 CCZ014, A A = ε
-- (windows), and the joint paper's SB2, Σ01 Σ01 = CCZ014.  Written by
-- `scratchpad/five/f6.py`.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module {MOD}.F6Ax where

open import Data.List using (List ; [] ; _∷_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
{dep_lines}

{NL.join(defs)}"""
