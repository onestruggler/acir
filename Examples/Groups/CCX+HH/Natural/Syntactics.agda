------------------------------------------------------------------------
-- Presentations of groups
--
-- Natural circuit rules for X, CX, CCX and HH.
--
-- The rules were found by the search in CCX+HH/Rules (see its README):
-- the involutions, four rules on two wires and eight on three are
-- complete on one, two and three wires (checked there by coset
-- enumeration), and two rules on four wires remove the parity of the
-- Toffoli count, which the true group lacks from four wires on.  Each
-- rule is stated on the bottom wires; Lift-Relation adds the structural
-- rules (placement one wire up, commutation of gates on disjoint
-- wires).  `XC` is the CNOT from wire 0 to wire 1 and `Ex` the swap of
-- the two bottom wires (CCX+HH.Syntactics).  Words are read in
-- matrix-product order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.Syntactics where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.Syntactics public
  using (Gate ; X-gate ; CX-gate ; CCX-gate ; HH-gate ; Gen ; Circuit
        ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥ ; _↑ ; _⇓
        ; X ; CX ; CCX ; HH ; XC ; Ex)
import Circuit.Base

private
  variable
    n : ℕ
  module SC = Circuit.Base Gate

infix 4 _N,_===_
data _N,_===_ : (n : ℕ) → WRel (Gen n) where
  -- every gate is an involution
  X²   : (₁₊ n) N, X • X === ε
  CX²  : (₂₊ n) N, CX • CX === ε
  CCX² : (₃₊ n) N, CCX • CCX === ε
  HH²  : (₂₊ n) N, HH • HH === ε
  -- two wires
  X-control  : (₂₊ n) N, X ↑ • CX • X ↑ === CX • X
  X-controlᵣ : (₂₊ n) N, XC • X • XC === X • X ↑
  CNOT-S3    : (₂₊ n) N, CX • XC • CX • XC • CX • XC === ε
  X-Z        : (₂₊ n) N, X • HH • X ↑ • HH === HH • X ↑ • HH • X
  -- three wires
  braid      : (₃₊ n) N, Ex • Ex ↑ • Ex === Ex ↑ • Ex • Ex ↑
  CX-up      : (₃₊ n) N, Ex • Ex ↑ • CX • Ex ↑ • Ex === CX ↑
  CCX-sym    : (₃₊ n) N, Ex ↑ • CCX • Ex ↑ === CCX
  CCX-neg    : (₃₊ n) N, X ↑ • CCX • X ↑ === CCX • Ex ↑ • CX • Ex ↑
  CCX-XC     : (₃₊ n) N, CCX • XC • CCX • XC === Ex • CCX • Ex • CCX
  HH-swap₀   : (₃₊ n) N, Ex • HH ↑ • Ex === HH • HH ↑
  HH-swap₁   : (₃₊ n) N, Ex ↑ • HH • Ex ↑ === HH • HH ↑
  CCX-HH     : (₃₊ n) N, CCX • XC • HH • XC === XC • HH • XC • CCX
  -- four wires
  CCX-comm   : (₄₊ n) N, CCX ↑ • CX • CCX ↑ • CX === Ex • CCX ↑ • Ex
  CCX-up     : (₄₊ n) N,
    Ex • Ex ↑ • Ex ↑ ↑ • CCX • Ex ↑ ↑ • Ex ↑ • Ex === CCX ↑

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
grouplike (gate₂ CX-gate) = CX , PB.axiom (srel CX²)
grouplike (gate₂ HH-gate) = HH , PB.axiom (srel HH²)
grouplike (gate₃ CCX-gate) = CCX , PB.axiom (srel CCX²)
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
