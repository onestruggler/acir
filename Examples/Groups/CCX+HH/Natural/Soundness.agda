------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural rules are sound at every width.
--
-- Each rule is derived in the complete translated calculus of
-- CCX+HH.Presentation: on its own wires by completeness, the two sides
-- having the same matrix (one boolean, CCX+HH.Decide), and on more
-- wires by adding idle wires on top (Structural.cong⇓; a closed word
-- one wire wider is the same word).  The structural rules are
-- Structural's.  So every derivation of the natural calculus is one of
-- the translated calculus, whose soundness gives that of the natural.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.Soundness where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.Natural.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
import Examples.Groups.CCX+HH.Semantics as Sem
import Examples.Groups.CCX+HH.Structural as St
open import Examples.Groups.CCX+HH.Decide using (by-eq)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Each rule on its own wires, in the translated calculus

private
  opaque
    unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

    X²₀ : P._≈_ {1} (X • X) ε
    X²₀ = P.completeness (by-eq tt)

    CX²₀ : P._≈_ {2} (CX • CX) ε
    CX²₀ = P.completeness (by-eq tt)

    CCX²₀ : P._≈_ {3} (CCX • CCX) ε
    CCX²₀ = P.completeness (by-eq tt)

    HH²₀ : P._≈_ {2} (HH • HH) ε
    HH²₀ = P.completeness (by-eq tt)

    X-control₀ : P._≈_ {2} (X ↑ • CX • X ↑) (CX • X)
    X-control₀ = P.completeness (by-eq tt)

    X-controlᵣ₀ : P._≈_ {2} (XC • X • XC) (X • X ↑)
    X-controlᵣ₀ = P.completeness (by-eq tt)

    CNOT-S3₀ : P._≈_ {2} (CX • XC • CX • XC • CX • XC) ε
    CNOT-S3₀ = P.completeness (by-eq tt)

    X-Z₀ : P._≈_ {2} (X • HH • X ↑ • HH) (HH • X ↑ • HH • X)
    X-Z₀ = P.completeness (by-eq tt)

    braid₀ : P._≈_ {3} (Ex • Ex ↑ • Ex) (Ex ↑ • Ex • Ex ↑)
    braid₀ = P.completeness (by-eq tt)

    CX-up₀ : P._≈_ {3} (Ex • Ex ↑ • CX • Ex ↑ • Ex) (CX ↑)
    CX-up₀ = P.completeness (by-eq tt)

    CCX-sym₀ : P._≈_ {3} (Ex ↑ • CCX • Ex ↑) CCX
    CCX-sym₀ = P.completeness (by-eq tt)

    CCX-neg₀ : P._≈_ {3} (X ↑ • CCX • X ↑) (CCX • Ex ↑ • CX • Ex ↑)
    CCX-neg₀ = P.completeness (by-eq tt)

    CCX-XC₀ : P._≈_ {3} (CCX • XC • CCX • XC) (Ex • CCX • Ex • CCX)
    CCX-XC₀ = P.completeness (by-eq tt)

    HH-swap₀₀ : P._≈_ {3} (Ex • HH ↑ • Ex) (HH • HH ↑)
    HH-swap₀₀ = P.completeness (by-eq tt)

    HH-swap₁₀ : P._≈_ {3} (Ex ↑ • HH • Ex ↑) (HH • HH ↑)
    HH-swap₁₀ = P.completeness (by-eq tt)

    CCX-HH₀ : P._≈_ {3} (CCX • XC • HH • XC) (XC • HH • XC • CCX)
    CCX-HH₀ = P.completeness (by-eq tt)

    CCX-comm₀ : P._≈_ {4} (CCX ↑ • CX • CCX ↑ • CX) (Ex • CCX ↑ • Ex)
    CCX-comm₀ = P.completeness (by-eq tt)

    CCX-up₀ : P._≈_ {4} (Ex • Ex ↑ • Ex ↑ ↑ • CCX • Ex ↑ ↑ • Ex ↑ • Ex) (CCX ↑)
    CCX-up₀ = P.completeness (by-eq tt)

------------------------------------------------------------------------
-- On the bottom wires of any wider circuit

-- A rule on k wires, from its instance on exactly k wires, by idle top
-- wires one at a time.
private
  X²ₙ : ∀ n → P._≈_ {₁₊ n} (X • X) ε
  X²ₙ zero = X²₀
  X²ₙ (suc n) = St.cong⇓ (X²ₙ n)

  CX²ₙ : ∀ n → P._≈_ {₂₊ n} (CX • CX) ε
  CX²ₙ zero = CX²₀
  CX²ₙ (suc n) = St.cong⇓ (CX²ₙ n)

  CCX²ₙ : ∀ n → P._≈_ {₃₊ n} (CCX • CCX) ε
  CCX²ₙ zero = CCX²₀
  CCX²ₙ (suc n) = St.cong⇓ (CCX²ₙ n)

  HH²ₙ : ∀ n → P._≈_ {₂₊ n} (HH • HH) ε
  HH²ₙ zero = HH²₀
  HH²ₙ (suc n) = St.cong⇓ (HH²ₙ n)

  X-controlₙ : ∀ n → P._≈_ {₂₊ n} (X ↑ • CX • X ↑) (CX • X)
  X-controlₙ zero = X-control₀
  X-controlₙ (suc n) = St.cong⇓ (X-controlₙ n)

  X-controlᵣₙ : ∀ n → P._≈_ {₂₊ n} (XC • X • XC) (X • X ↑)
  X-controlᵣₙ zero = X-controlᵣ₀
  X-controlᵣₙ (suc n) = St.cong⇓ (X-controlᵣₙ n)

  CNOT-S3ₙ : ∀ n → P._≈_ {₂₊ n} (CX • XC • CX • XC • CX • XC) ε
  CNOT-S3ₙ zero = CNOT-S3₀
  CNOT-S3ₙ (suc n) = St.cong⇓ (CNOT-S3ₙ n)

  X-Zₙ : ∀ n → P._≈_ {₂₊ n} (X • HH • X ↑ • HH) (HH • X ↑ • HH • X)
  X-Zₙ zero = X-Z₀
  X-Zₙ (suc n) = St.cong⇓ (X-Zₙ n)

  braidₙ : ∀ n → P._≈_ {₃₊ n} (Ex • Ex ↑ • Ex) (Ex ↑ • Ex • Ex ↑)
  braidₙ zero = braid₀
  braidₙ (suc n) = St.cong⇓ (braidₙ n)

  CX-upₙ : ∀ n → P._≈_ {₃₊ n} (Ex • Ex ↑ • CX • Ex ↑ • Ex) (CX ↑)
  CX-upₙ zero = CX-up₀
  CX-upₙ (suc n) = St.cong⇓ (CX-upₙ n)

  CCX-symₙ : ∀ n → P._≈_ {₃₊ n} (Ex ↑ • CCX • Ex ↑) CCX
  CCX-symₙ zero = CCX-sym₀
  CCX-symₙ (suc n) = St.cong⇓ (CCX-symₙ n)

  CCX-negₙ : ∀ n → P._≈_ {₃₊ n} (X ↑ • CCX • X ↑) (CCX • Ex ↑ • CX • Ex ↑)
  CCX-negₙ zero = CCX-neg₀
  CCX-negₙ (suc n) = St.cong⇓ (CCX-negₙ n)

  CCX-XCₙ : ∀ n → P._≈_ {₃₊ n} (CCX • XC • CCX • XC) (Ex • CCX • Ex • CCX)
  CCX-XCₙ zero = CCX-XC₀
  CCX-XCₙ (suc n) = St.cong⇓ (CCX-XCₙ n)

  HH-swap₀ₙ : ∀ n → P._≈_ {₃₊ n} (Ex • HH ↑ • Ex) (HH • HH ↑)
  HH-swap₀ₙ zero = HH-swap₀₀
  HH-swap₀ₙ (suc n) = St.cong⇓ (HH-swap₀ₙ n)

  HH-swap₁ₙ : ∀ n → P._≈_ {₃₊ n} (Ex ↑ • HH • Ex ↑) (HH • HH ↑)
  HH-swap₁ₙ zero = HH-swap₁₀
  HH-swap₁ₙ (suc n) = St.cong⇓ (HH-swap₁ₙ n)

  CCX-HHₙ : ∀ n → P._≈_ {₃₊ n} (CCX • XC • HH • XC) (XC • HH • XC • CCX)
  CCX-HHₙ zero = CCX-HH₀
  CCX-HHₙ (suc n) = St.cong⇓ (CCX-HHₙ n)

  CCX-commₙ : ∀ n → P._≈_ {₄₊ n} (CCX ↑ • CX • CCX ↑ • CX) (Ex • CCX ↑ • Ex)
  CCX-commₙ zero = CCX-comm₀
  CCX-commₙ (suc n) = St.cong⇓ (CCX-commₙ n)

  CCX-upₙ : ∀ n → P._≈_ {₄₊ n}
    (Ex • Ex ↑ • Ex ↑ ↑ • CCX • Ex ↑ ↑ • Ex ↑ • Ex) (CCX ↑)
  CCX-upₙ zero = CCX-up₀
  CCX-upₙ (suc n) = St.cong⇓ (CCX-upₙ n)

------------------------------------------------------------------------
-- Every derivation of the natural calculus is one of the translated

axiom-P : ∀ {n w v} → n VRel, w === v → w P.≈ v
axiom-P (srel (X² {n})) = X²ₙ n
axiom-P (srel (CX² {n})) = CX²ₙ n
axiom-P (srel (CCX² {n})) = CCX²ₙ n
axiom-P (srel (HH² {n})) = HH²ₙ n
axiom-P (srel (X-control {n})) = X-controlₙ n
axiom-P (srel (X-controlᵣ {n})) = X-controlᵣₙ n
axiom-P (srel (CNOT-S3 {n})) = CNOT-S3ₙ n
axiom-P (srel (X-Z {n})) = X-Zₙ n
axiom-P (srel (braid {n})) = braidₙ n
axiom-P (srel (CX-up {n})) = CX-upₙ n
axiom-P (srel (CCX-sym {n})) = CCX-symₙ n
axiom-P (srel (CCX-neg {n})) = CCX-negₙ n
axiom-P (srel (CCX-XC {n})) = CCX-XCₙ n
axiom-P (srel (HH-swap₀ {n})) = HH-swap₀ₙ n
axiom-P (srel (HH-swap₁ {n})) = HH-swap₁ₙ n
axiom-P (srel (CCX-HH {n})) = CCX-HHₙ n
axiom-P (srel (CCX-comm {n})) = CCX-commₙ n
axiom-P (srel (CCX-up {n})) = CCX-upₙ n
axiom-P (cong↑ r) = St.cong↑ (axiom-P r)
axiom-P (comm₁ h g) = St.comm₁ [ g ]ʷ h
axiom-P (comm₂ h g) = St.comm₂ [ g ]ʷ h
axiom-P (comm₃ h g) = St.comm₃ [ g ]ʷ h
axiom-P (LR-ω↑=ω ())

natural⇒translated : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → w P.≈ v
natural⇒translated PB.refl = PB.refl
natural⇒translated (PB.sym p) = PB.sym (natural⇒translated p)
natural⇒translated (PB.trans p q) = PB.trans (natural⇒translated p) (natural⇒translated q)
natural⇒translated (PB.cong p q) = PB.cong (natural⇒translated p) (natural⇒translated q)
natural⇒translated PB.assoc = PB.assoc
natural⇒translated PB.left-unit = PB.left-unit
natural⇒translated PB.right-unit = PB.right-unit
natural⇒translated (PB.axiom a) = axiom-P a

-- The natural rules are sound for the ordinary circuit matrices.
sound : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → Sem.interpret w ≡ Sem.interpret v
sound p = P.soundness (natural⇒translated p)
