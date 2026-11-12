import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import appA

HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Appendix A: the gates are involutions
--
-- The two derivations of the paper's Appendix A, in diagram order (the
-- paper writes composition order, so each of its products is read
-- backwards here).  They take place in the PROP, where gates have no
-- formal inverses, and cancel a circuit only after exhibiting an
-- inverse for it as an equation (awy⁼, xvb⁼, Lmd⁼, Ld⁼).
--
-- The CNOT, on two wires: x = X on wire 1, y = X on wire 0, a = CX,
-- b = σ CX σ (the paper's CX_{2→1}), w = x a x and v = y b y; (2) reads
-- a w = y and (3) a b a = σ.  The lemmas follow the paper's (i)–(vi),
-- and CX²⁼ is a a = a (b a a b) a = (a b a)(a b a) = σ σ = ε.
--
-- The Toffoli gate, on three wires: x = X on wire 2, c = CCX,
-- e = σ c σ (CCX_{13→2}), W = x c x, m = x e x, q = CX, p = σ CX σ and
-- d = p c p; (4) reads c W = q and (6) d = e c e.  The lemmas follow
-- the paper's (i)–(viii), and CCX²⁼ is c c = σ e e σ = σ x m m x σ = ε.
--
-- Every lemma is an equation on the bottom wires of a circuit of any
-- width.  The derivations are generated (scripts derive.py and appA.py
-- of the folder's gen/) from the paper's chains of steps, each step one
-- rewrite up to the commutation of letters on disjoint wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Involutions where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.XCXCCX-4bit.Syntactics using (_↥)
open import Examples.Groups.XCXCCX-4bit.Kit

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The CNOT

'''

MID = r'''
------------------------------------------------------------------------
-- The Toffoli gate

'''

txt = HDR + '\n'.join(appA.cnot).rstrip() + '\n' + MID + '\n'.join(appA.toffoli).rstrip() + '\n'
with open(sys.argv[1], 'w', encoding='utf-8', newline='\n') as f:
    f.write(txt)
print('lines', txt.count('\n'))
