------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural rules for CCX+H are sound at every width.
--
-- Each rule is derived in the complete translated calculus of
-- CCX+H.Presentation: on its own wires by completeness, the two sides
-- having the same matrix (one boolean, CCX+HH.Decide), and on more
-- wires by adding idle wires on top (Structural.cong⇓; a closed word
-- one wire wider is the same word).  The structural rules are
-- Structural's.  So every derivation of the natural calculus is one of
-- the translated calculus, whose soundness gives that of the natural.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Natural.Soundness where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.Natural.Syntactics
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Structural as St
open import Examples.Groups.CCX+HH.Decide using (by-eq√)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R

------------------------------------------------------------------------
-- Each rule on its own wires, in the translated calculus

private
  opaque
    unfolding S.actV S.set₁ S.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

    X²₀ : 1 P.⊢ X • X ≈ ε
    X²₀ = P.complete 1 (by-eq√ tt)

    H²₀ : 1 P.⊢ H • H ≈ ε
    H²₀ = P.complete 1 (by-eq√ tt)

    CX²₀ : 2 P.⊢ CX • CX ≈ ε
    CX²₀ = P.complete 2 (by-eq√ tt)

    CCX²₀ : 3 P.⊢ CCX • CCX ≈ ε
    CCX²₀ = P.complete 3 (by-eq√ tt)

    XH⁸₀ : 1 P.⊢ X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H ≈ ε
    XH⁸₀ = P.complete 1 (by-eq√ tt)

    X-controlᵣ₀ : 2 P.⊢ XC • X • XC ≈ X • X ↑
    X-controlᵣ₀ = P.complete 2 (by-eq√ tt)

    H-swap₀ : 2 P.⊢ Ex • H • Ex ≈ H ↑
    H-swap₀ = P.complete 2 (by-eq√ tt)

    CZ-XC₀ : 2 P.⊢ CZ • XC • CZ • XC ≈ Z
    CZ-XC₀ = P.complete 2 (by-eq√ tt)

------------------------------------------------------------------------
-- On the bottom wires of any wider circuit

private
  X²ₙ : ∀ n → (₁₊ n) P.⊢ X • X ≈ ε
  X²ₙ zero = X²₀
  X²ₙ (suc n) = St.cong⇓ (X²ₙ n)

  H²ₙ : ∀ n → (₁₊ n) P.⊢ H • H ≈ ε
  H²ₙ zero = H²₀
  H²ₙ (suc n) = St.cong⇓ (H²ₙ n)

  CX²ₙ : ∀ n → (₂₊ n) P.⊢ CX • CX ≈ ε
  CX²ₙ zero = CX²₀
  CX²ₙ (suc n) = St.cong⇓ (CX²ₙ n)

  CCX²ₙ : ∀ n → (₃₊ n) P.⊢ CCX • CCX ≈ ε
  CCX²ₙ zero = CCX²₀
  CCX²ₙ (suc n) = St.cong⇓ (CCX²ₙ n)

  XH⁸ₙ : ∀ n → (₁₊ n) P.⊢ X • H • X • H • X • H • X • H • X • H • X • H • X • H • X • H ≈ ε
  XH⁸ₙ zero = XH⁸₀
  XH⁸ₙ (suc n) = St.cong⇓ (XH⁸ₙ n)

  X-controlᵣₙ : ∀ n → (₂₊ n) P.⊢ XC • X • XC ≈ X • X ↑
  X-controlᵣₙ zero = X-controlᵣ₀
  X-controlᵣₙ (suc n) = St.cong⇓ (X-controlᵣₙ n)

  H-swapₙ : ∀ n → (₂₊ n) P.⊢ Ex • H • Ex ≈ H ↑
  H-swapₙ zero = H-swap₀
  H-swapₙ (suc n) = St.cong⇓ (H-swapₙ n)

  CZ-XCₙ : ∀ n → (₂₊ n) P.⊢ CZ • XC • CZ • XC ≈ Z
  CZ-XCₙ zero = CZ-XC₀
  CZ-XCₙ (suc n) = St.cong⇓ (CZ-XCₙ n)

------------------------------------------------------------------------
-- Every derivation of the natural calculus is one of the translated

axiom-P : ∀ {n w v} → n VRel, w === v → n P.⊢ w ≈ v
axiom-P (srel (X² {n})) = X²ₙ n
axiom-P (srel (H² {n})) = H²ₙ n
axiom-P (srel (CX² {n})) = CX²ₙ n
axiom-P (srel (CCX² {n})) = CCX²ₙ n
axiom-P (srel (XH⁸ {n})) = XH⁸ₙ n
axiom-P (srel (X-controlᵣ {n})) = X-controlᵣₙ n
axiom-P (srel (H-swap {n})) = H-swapₙ n
axiom-P (srel (CZ-XC {n})) = CZ-XCₙ n
axiom-P (cong↑ r) = St.cong↑ (axiom-P r)
axiom-P (comm₁ h g) = St.comm₁ [ g ]ʷ h
axiom-P (comm₂ h g) = St.comm₂ [ g ]ʷ h
axiom-P (comm₃ h g) = St.comm₃ [ g ]ʷ h
axiom-P (LR-ω↑=ω ())

natural⇒translated : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → n P.⊢ w ≈ v
natural⇒translated PB.refl = PB.refl
natural⇒translated (PB.sym p) = PB.sym (natural⇒translated p)
natural⇒translated (PB.trans p q) = PB.trans (natural⇒translated p) (natural⇒translated q)
natural⇒translated (PB.cong p q) = PB.cong (natural⇒translated p) (natural⇒translated q)
natural⇒translated PB.assoc = PB.assoc
natural⇒translated PB.left-unit = PB.left-unit
natural⇒translated PB.right-unit = PB.right-unit
natural⇒translated (PB.axiom a) = axiom-P a

-- The natural rules are sound for the ordinary circuit matrices.
sound : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → P.interpret w ≡ P.interpret v
sound {n} p = P.sound n (natural⇒translated p)
