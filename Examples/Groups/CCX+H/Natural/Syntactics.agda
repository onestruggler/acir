------------------------------------------------------------------------
-- Presentations of groups
--
-- Natural rules for X, CX, CCX and H, found by coset enumeration
-- (CCX+HH/Rules/naturalH2.py) and proved complete on one and two wires
-- (Natural/Width1, Natural/Width2).  Besides the involutions, one rule
-- on one wire and three on two:
--
--   (X H)⁸ = 1            the one-wire group is dihedral of order 16
--   XC X XC = X X↑         X on the target of the reversed CNOT spreads
--   Ex H Ex = H↑           the swap moves H to the other wire
--   CZ XC CZ XC = Z        CZ and the reversed CNOT commute up to Z
--
-- with XC = H H↑ CX H↑ H the CNOT from wire 0 to wire 1, Ex = CX XC CX
-- the swap, CZ = H CX H and Z = H X H.  Wire 0 is the bottom wire and
-- CX's control is wire 1.  The structural rules are Circuit.Base's.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Natural.Syntactics where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.Syntactics public
  using (Gate ; X-gate ; H-gate ; CX-gate ; CCX-gate ; Gen ; Circuit
        ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥ ; _↑ ; _⇓
        ; X ; H ; CX ; CCX)
import Circuit.Base

private
  variable
    n : ℕ
  module SC = Circuit.Base Gate

-- The reversed CNOT, the swap, CZ and Z.
XC Ex CZ : Circuit (₂₊ n)
XC = H • H ↑ • CX • H ↑ • H
Ex = CX • XC • CX
CZ = H • CX • H

Z : Circuit (₁₊ n)
Z = H • X • H

infix 4 _N,_===_
data _N,_===_ : (n : ℕ) → WRel (Gen n) where
  -- every gate is an involution
  X²   : (₁₊ n) N, X • X === ε
  H²   : (₁₊ n) N, H • H === ε
  CX²  : (₂₊ n) N, CX • CX === ε
  CCX² : (₃₊ n) N, CCX • CCX === ε
  -- one wire
  XH⁸  : (₁₊ n) N, X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H === ε
  -- two wires
  X-controlᵣ : (₂₊ n) N, XC • X • XC === X • X ↑
  H-swap     : (₂₊ n) N, Ex • H • Ex === H ↑
  CZ-XC      : (₂₊ n) N, CZ • XC • CZ • XC === Z

private module LR = SC.Lift-Relation _N,_===_
open LR public
  using (srel ; cong↑ ; comm₁ ; comm₂ ; comm₃ ; lemma-cong↑ ; _VRel,_===_)
  renaming (ω↑=ω to LR-ω↑=ω)

infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v

grouplike : Grouplike (_VRel,_===_ n)
grouplike (gate₀ ())
grouplike (gate₁ X-gate) = X , PB.axiom (srel X²)
grouplike (gate₁ H-gate) = H , PB.axiom (srel H²)
grouplike (gate₂ CX-gate) = CX , PB.axiom (srel CX²)
grouplike (gate₃ CCX-gate) = CCX , PB.axiom (srel CCX²)
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
