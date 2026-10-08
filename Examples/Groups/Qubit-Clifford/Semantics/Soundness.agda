------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness: equal circuits have equal matrices
--
-- Each of C1 … C15 is checked on Gaussian matrices at the width it is
-- drawn on (Interpretation.rel-sound≡, which also reads it at every
-- larger width); the side with more gates H and ω goes first, so C10
-- and C11, whose right sides carry ω⁷, are checked right to left.  The
-- structural rules are the tensor calculus.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.Soundness
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i² hiding (_^_)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The relations

srel-sound : n SRel, w === v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
srel-sound {w = w} {v = v} C₁ = rel-sound≡ {k = 0}
  (ω ^ 8)
  ε
  4 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₂ = rel-sound≡ {k = 1}
  (H • H)
  ε
  1 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₃ = rel-sound≡ {k = 1}
  (S • S • S • S)
  ε
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₄ = rel-sound≡ {k = 1}
  (S • H • S • H • S • H)
  ω
  1 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₅ = rel-sound≡ {k = 2}
  (CZ • CZ)
  ε
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₆ = rel-sound≡ {k = 2}
  (CZ • S ↑)
  (S ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₇ = rel-sound≡ {k = 2}
  (CZ • S)
  (S • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₈ = rel-sound≡ {k = 2}
  (CZ • H ↑ • S ↑ • S ↑ • H ↑)
  (H ↑ • S ↑ • S ↑ • H ↑ • S • S • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₉ = rel-sound≡ {k = 2}
  (CZ • H • S • S • H)
  (H • S • S • H • S ↑ • S ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₁₀ = ≐-sym (rel-sound≡ {k = 2}
  (ω ^ 7 • S ↑ • H ↑ • S ↑ • S • CZ • H ↑ • S ↑)
  (CZ • H ↑ • CZ)
  4 {v} {w} Eq.refl Eq.refl Eq.refl Eq.refl)
srel-sound {w = w} {v = v} C₁₁ = ≐-sym (rel-sound≡ {k = 2}
  (ω ^ 7 • S • H • S • S ↑ • CZ • H • S)
  (CZ • H • CZ)
  4 {v} {w} Eq.refl Eq.refl Eq.refl Eq.refl)
srel-sound {w = w} {v = v} C₁₂ = rel-sound≡ {k = 3}
  (CZ • CZ ↑)
  (CZ ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₁₃ = rel-sound≡ {k = 3}
  (CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • H • H ↑ • CZ • H • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑)
  (CZ • H ↑ • H • CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ ↑ • H ↑ • CZ • H ↑ • H • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₁₄ = rel-sound≡ {k = 3}
  (CZ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ •
   H ↑ • H ↑ ↑ • CZ ↑ • CZ • H ↑ • H ↑ ↑ • CZ ↑ • H ↑ • H ↑ ↑ • CZ ↑)
  ε
  6 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} C₁₅ = rel-sound≡ {k = 3}
  (CZ ↑ • H • H ↑ • CZ • H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ •
   H ↑ • H • CZ • CZ ↑ • H ↑ • H • CZ • H ↑ • H • CZ)
  ε
  6 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl

------------------------------------------------------------------------
-- The structural rules

⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ᴬ ≐ up ⟦ w ⟧ᴬ
⟦↑⟧ [ g ]ʷ  = ≐-refl _
⟦↑⟧ ε       = ≐-sym up-Id
⟦↑⟧ (w • v) = ≐-trans (⊙-cong (⟦↑⟧ w) (⟦↑⟧ v)) (up-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ)

vrel-sound : n VRel, w === v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
vrel-sound (srel r)    = srel-sound r
vrel-sound (cong↑ {w = w} {v = v} r) =
  ≐-trans (⟦↑⟧ w) (≐-trans (up-cong (vrel-sound r)) (≐-sym (⟦↑⟧ v)))
vrel-sound (comm₀ ω-gate g) = ≐-sym (scal-central ω̂ (valA g))
vrel-sound (comm₁ H-gate g) = ≐-sym (emb-up-comm {k = 1} (scale s (ιO (GI.ix hG))) (valA g))
vrel-sound (comm₁ S-gate g) = ≐-sym (emb-up-comm {k = 1} (ιO (GI.ix sG)) (valA g))
vrel-sound (comm₂ CZ-gate g) =
  ≐-trans (⊙-cong {M = up (up G)} {M' = upk 2 G} {N = C} {N' = C} (up-up G) (≐-refl C))
    (≐-trans (≐-sym (emb-up-comm {k = 2} (ιO (GI.ix czG)) G))
      (⊙-cong {M = C} {M' = C} {N = upk 2 G} {N' = up (up G)} (≐-refl C) (≐-sym (up-up G))))
  where
  G = valA g
  C = emb {2} (ιO (GI.ix czG))
vrel-sound (ω↑=ω ω-gate) = up-scal ω̂

sound : n ⊢ w ≈ v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
sound PB.refl          = ≐-refl _
sound (PB.sym e)       = ≐-sym (sound e)
sound (PB.trans e f)   = ≐-trans (sound e) (sound f)
sound (PB.cong e f)    = ⊙-cong (sound e) (sound f)
sound PB.assoc         = ⊙-assoc _ _ _
sound PB.left-unit     = ⊙-identityˡ _
sound PB.right-unit    = ⊙-identityʳ _
sound (PB.axiom r)     = vrel-sound r
