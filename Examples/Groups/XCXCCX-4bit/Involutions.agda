------------------------------------------------------------------------
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

-- (i) w a = y
xaxa⁼ : Eqn (₂₊ n)
xaxa⁼ = derive (Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ [])
  (Xₗ ∷ [])
  (perm (Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ []) ∷
     rw 4 (sym⁼ (lift⁼ r1⁼)) ∷
     perm (Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ Xₗ ↥ ∷ []) ∷
     rw 1 (r2⁼) ∷
     perm (Xₗ ∷ Xₗ ↥ ∷ Xₗ ↥ ∷ []) ∷
     rw 1 (lift⁼ r1⁼) ∷ [])
  refl

-- (ii) a y = y a
ay⁼ : Eqn (₂₊ n)
ay⁼ = derive (CXₗ ∷ Xₗ ∷ [])
  (Xₗ ∷ CXₗ ∷ [])
  (perm (CXₗ ∷ Xₗ ∷ []) ∷
     rw 1 (sym⁼ xaxa⁼) ∷
     perm (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ []) ∷
     rw 0 (r2⁼) ∷ [])
  refl

-- (iii) a x a = y x
axa⁼ : Eqn (₂₊ n)
axa⁼ = derive (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ [])
  (Xₗ ∷ Xₗ ↥ ∷ [])
  (perm (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ []) ∷
     rw 3 (sym⁼ (lift⁼ r1⁼)) ∷
     perm (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (r2⁼) ∷ [])
  refl

-- X on wire 1 past the swap
xσ⁼ : Eqn (₂₊ n)
xσ⁼ = derive (Xₗ ↥ ∷ σₗ ∷ [])
  (σₗ ∷ Xₗ ∷ [])
  (perm (Xₗ ↥ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ↥ ∷ σₗ ∷ []) ∷
     rw 1 (sym⁼ σX⁼) ∷
     perm (σₗ ∷ Xₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 2 (σσ⁼) ∷ [])
  refl

-- (i') v b = x
vb⁼ : Eqn (₂₊ n)
vb⁼ = derive (Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (Xₗ ↥ ∷ [])
  (perm (Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (σX⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 4 (σX⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 3 (σσ⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 1 (xaxa⁼) ∷
     perm (σₗ ∷ Xₗ ∷ σₗ ∷ []) ∷
     rw 1 (σX⁼) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl

-- (iii') b y b = x y
byb⁼ : Eqn (₂₊ n)
byb⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (Xₗ ↥ ∷ Xₗ ∷ [])
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 3 (σX⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 2 (σσ⁼) ∷
     perm (σₗ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 1 (axa⁼) ∷
     perm (σₗ ∷ Xₗ ∷ Xₗ ↥ ∷ σₗ ∷ []) ∷
     rw 2 (xσ⁼) ∷
     perm (σₗ ∷ Xₗ ∷ σₗ ∷ Xₗ ∷ []) ∷
     rw 1 (σX⁼) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (σσ⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ∷ []) ∷ [])
  refl

-- x y b a = a a b y a
xyba⁼ : Eqn (₂₊ n)
xyba⁼ = derive (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ [])
  (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ CXₗ ∷ [])
  (perm (Xₗ ∷ Xₗ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ []) ∷
     rw 0 (sym⁼ axa⁼) ∷
     perm (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ []) ∷
     rw 2 (r3⁼) ∷
     perm (CXₗ ∷ Xₗ ↥ ∷ σₗ ∷ []) ∷
     rw 1 (xσ⁼) ∷
     perm (CXₗ ∷ σₗ ∷ Xₗ ∷ []) ∷
     rw 1 (sym⁼ r3⁼) ∷
     perm (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ∷ []) ∷
     rw 5 (ay⁼) ∷ [])
  refl

-- a w y = ε
awy⁼ : Eqn (₂₊ n)
awy⁼ = derive (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ Xₗ ∷ [])
  []
  (perm (CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ Xₗ ∷ []) ∷
     rw 0 (r2⁼) ∷
     perm (Xₗ ∷ Xₗ ∷ []) ∷
     rw 0 (r1⁼) ∷ [])
  refl

-- (iv) x y b = a a b y
xyb⁼ : Eqn (₂₊ n)
xyb⁼ = derive (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ [])
  (perm (Xₗ ∷ Xₗ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 5 (sym⁼ awy⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (xyba⁼) ∷
     perm (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ CXₗ ∷ Xₗ ↥ ∷ CXₗ ∷ Xₗ ↥ ∷ Xₗ ∷ []) ∷
     rw 6 (awy⁼) ∷ [])
  refl

-- (v) a a b b = ε
aabb⁼ : Eqn (₂₊ n)
aabb⁼ = derive (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 5 (sym⁼ r1⁼) ∷
     perm (CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ xyb⁼) ∷
     perm (Xₗ ∷ Xₗ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 2 (byb⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ↥ ∷ Xₗ ∷ Xₗ ∷ []) ∷
     rw 2 (r1⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (lift⁼ r1⁼) ∷ [])
  refl

-- b b a a = ε
bbaa⁼ : Eqn (₂₊ n)
bbaa⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ [])
  []
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ []) ∷
     rw 2 (σσ⁼) ∷
     perm (σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ []) ∷
     rw 5 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ []) ∷
     rw 8 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 1 (aabb⁼) ∷
     perm (σₗ ∷ σₗ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl

-- x v b = ε
xvb⁼ : Eqn (₂₊ n)
xvb⁼ = derive (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 1 (vb⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ↥ ∷ []) ∷
     rw 0 (lift⁼ r1⁼) ∷ [])
  refl

-- (vi) b a a b = ε
baab⁼ : Eqn (₂₊ n)
baab⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ xvb⁼) ∷
     perm (Xₗ ∷ Xₗ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 6 (bbaa⁼) ∷
     perm (Xₗ ↥ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (xvb⁼) ∷ [])
  refl

-- The CNOT is an involution.
CX²⁼ : Eqn (₂₊ n)
CX²⁼ = derive (CXₗ ∷ CXₗ ∷ [])
  []
  (perm (CXₗ ∷ CXₗ ∷ []) ∷
     rw 1 (sym⁼ baab⁼) ∷
     perm (CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ []) ∷
     rw 0 (r3⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ []) ∷
     rw 1 (r3⁼) ∷
     perm (σₗ ∷ σₗ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl

------------------------------------------------------------------------
-- The Toffoli gate

-- p p = ε
pp⁼ : Eqn (₃₊ n)
pp⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 2 (σσ⁼) ∷
     perm (σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 1 (CX²⁼) ∷
     perm (σₗ ∷ σₗ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl

-- (i) W c = q
Wc⁼ : Eqn (₃₊ n)
Wc⁼ = derive (Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ [])
  (CXₗ ∷ [])
  (perm (Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ []) ∷
     rw 4 (sym⁼ (lift⁼ (lift⁼ r1⁼))) ∷
     perm (Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 1 (r4⁼) ∷
     perm (CXₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 1 (lift⁼ (lift⁼ r1⁼)) ∷ [])
  refl

-- (ii) c q = q c
cq⁼ : Eqn (₃₊ n)
cq⁼ = derive (CCXₗ ∷ CXₗ ∷ [])
  (CXₗ ∷ CCXₗ ∷ [])
  (perm (CCXₗ ∷ CXₗ ∷ []) ∷
     rw 1 (sym⁼ Wc⁼) ∷
     perm (CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ []) ∷
     rw 0 (r4⁼) ∷ [])
  refl

-- e m = p
em⁼ : Eqn (₃₊ n)
em⁼ = derive (σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  (σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (perm (σₗ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 3 (σσ⁼) ∷
     perm (σₗ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ []) ∷
     rw 1 (r4⁼) ∷ [])
  refl

-- m e = p
me⁼ : Eqn (₃₊ n)
me⁼ = derive (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ [])
  (σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ []) ∷
     rw 4 (σσ⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ []) ∷
     rw 1 (Wc⁼) ∷ [])
  refl

-- p q p = σ
pqp⁼ : Eqn (₃₊ n)
pqp⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (σₗ ∷ [])
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 1 (r3⁼) ∷
     perm (σₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl

-- (iii) c e c = d
cec⁼ : Eqn (₃₊ n)
cec⁼ = derive (CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ [])
  (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (perm (CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 0 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 7 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 1 (sym⁼ r6⁼) ∷
     perm (σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ pqp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 14 (sym⁼ pqp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 4 (pp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 5 (pp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CCXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 3 (sym⁼ cq⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 4 (CX²⁼) ∷ [])
  refl

-- (iv) d = m d m
mdm⁼ : Eqn (₃₊ n)
mdm⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ me⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 9 (sym⁼ em⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 5 (sym⁼ r6⁼) ∷
     perm (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷ [])
  refl

-- (v) d c = e d
dc⁼ : Eqn (₃₊ n)
dc⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ [])
  (σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 0 (sym⁼ cec⁼) ∷
     perm (CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ CCXₗ ∷ []) ∷
     rw 0 (cec⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 0 (r6⁼) ∷
     perm (σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 3 (cec⁼) ∷ [])
  refl

-- e m = m e
em=me⁼ : Eqn (₃₊ n)
em=me⁼ = derive (σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ [])
  (perm (σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 0 (em⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ me⁼) ∷ [])
  refl

-- (p q W e) m d = ε
Lmd⁼ : Eqn (₃₊ n)
Lmd⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 7 (em⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 7 (pp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 4 (Wc⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 3 (CX²⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (pp⁼) ∷ [])
  refl

-- (vi) m c = c m
mc⁼ : Eqn (₃₊ n)
mc⁼ = derive (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ [])
  (CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  (perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ []) ∷
     rw 0 (sym⁼ Lmd⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ []) ∷
     rw 10 (sym⁼ mdm⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 10 (dc⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 13 (mdm⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 10 (em=me⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 15 (sym⁼ dc⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 0 (Lmd⁼) ∷
     perm (CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷ [])
  refl

-- (vii) d m = m d
dm⁼ : Eqn (₃₊ n)
dm⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 0 (r6⁼) ∷
     perm (σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 4 (em=me⁼) ∷
     perm (σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ []) ∷
     rw 3 (sym⁼ mc⁼) ∷
     perm (σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ []) ∷
     rw 0 (em=me⁼) ∷
     perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ []) ∷
     rw 5 (sym⁼ r6⁼) ∷
     perm (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷ [])
  refl

-- (p q W p) d = ε
Ld⁼ : Eqn (₃₊ n)
Ld⁼ = derive (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ [])
  []
  (perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 7 (pp⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 4 (Wc⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 3 (CX²⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (pp⁼) ∷ [])
  refl

-- (viii) m m = ε
mm⁼ : Eqn (₃₊ n)
mm⁼ = derive (Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ [])
  []
  (perm (σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 0 (sym⁼ Ld⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 10 (dm⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 10 (sym⁼ mdm⁼) ∷
     perm (σₗ ∷ CXₗ ∷ σₗ ∷ CXₗ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ CXₗ ∷ σₗ ∷ []) ∷
     rw 0 (Ld⁼) ∷ [])
  refl

-- The Toffoli gate is an involution.
CCX²⁼ : Eqn (₃₊ n)
CCX²⁼ = derive (CCXₗ ∷ CCXₗ ∷ [])
  []
  (perm (CCXₗ ∷ CCXₗ ∷ []) ∷
     rw 0 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ CCXₗ ∷ CCXₗ ∷ []) ∷
     rw 3 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ []) ∷
     rw 6 (sym⁼ σσ⁼) ∷
     perm (σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 0 (sym⁼ (lift⁼ (lift⁼ r1⁼))) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 5 (sym⁼ (lift⁼ (lift⁼ r1⁼))) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ CCXₗ ∷ σₗ ∷ σₗ ∷ []) ∷
     rw 10 (sym⁼ (lift⁼ (lift⁼ r1⁼))) ∷
     perm (σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ CCXₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 2 (mm⁼) ∷
     perm (σₗ ∷ σₗ ∷ Xₗ ↥ ↥ ∷ Xₗ ↥ ↥ ∷ []) ∷
     rw 2 (lift⁼ (lift⁼ r1⁼)) ∷
     perm (σₗ ∷ σₗ ∷ []) ∷
     rw 0 (σσ⁼) ∷ [])
  refl
