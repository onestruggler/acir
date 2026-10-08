------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness: equal circuits have equal matrices
--
-- Each of R1 … R16 is checked on integer matrices at the width it is
-- drawn on (Interpretation.rel-sound≡, which also reads it at every
-- larger width); the structural rules are the tensor calculus.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.Soundness
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  where

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR
open import Examples.Groups.Real-Clifford.Semantics.Interpretation isCR s s-half hiding (_^_)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The relations

srel-sound : n SRel, w === v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
srel-sound {w = w} {v = v} R₁ = rel-sound≡ {k = 0}
  (neg • neg)
  ε
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₂ = rel-sound≡ {k = 1}
  (Z • Z)
  ε
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₃ = rel-sound≡ {k = 1}
  (H • H)
  ε
  1 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₄ = rel-sound≡ {k = 1}
  ((H • Z) ^ 4)
  neg
  2 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₅ = rel-sound≡ {k = 2}
  (CZ • CZ)
  ε
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₆ = rel-sound≡ {k = 2}
  (CZ • Z ↑)
  (Z ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₇ = rel-sound≡ {k = 2}
  (CZ • Z)
  (Z • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₈ = rel-sound≡ {k = 2}
  (CZ • H ↑ • Z ↑ • H ↑)
  (H ↑ • Z • Z ↑ • H ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₉ = rel-sound≡ {k = 2}
  (CZ • H • Z • H)
  (H • Z • Z ↑ • H • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₀ = rel-sound≡ {k = 2}
  (CZ • H ↑ • CZ • H ↑)
  (Z • H ↑ • CZ • H ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₁ = rel-sound≡ {k = 2}
  (CZ • H • CZ • H)
  (H • Z ↑ • CZ • H • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₂ = rel-sound≡ {k = 2}
  (CZ • HH • CZ • HH • CZ • H)
  (H ↑ • CZ • HH • CZ • HH • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₃ = rel-sound≡ {k = 3}
  (CZ • CZ ↑)
  (CZ ↑ • CZ)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₄ = rel-sound≡ {k = 3}
  (H • CZ • HH • CZ • H ↑ • CZ ↑ • H ↑ • CZ • HH • CZ • H)
  (H ↑ ↑ • CZ ↑ • HH ↑ • CZ ↑ • H ↑ • CZ • H ↑ • CZ ↑ • HH ↑ • CZ ↑ • H ↑ ↑)
  0 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₅ = rel-sound≡ {k = 3}
  (CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑ • CZ • HH ↑ • CZ ↑ • HH ↑ • CZ ↑)
  (CZ ↑ • HH ↑ • CZ ↑ • HH ↑ • CZ)
  2 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl
srel-sound {w = w} {v = v} R₁₆ = rel-sound≡ {k = 3}
  (CZ ↑ • HH • CZ • HH • CZ • CZ ↑ • HH • CZ • HH • CZ)
  (CZ • HH • CZ • HH • CZ ↑)
  2 {w} {v} Eq.refl Eq.refl Eq.refl Eq.refl

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
vrel-sound (comm₀ neg-gate g) = ≐-sym (scal-central (- 1#) (valA g))
vrel-sound (comm₁ H-gate g) = ≐-sym (emb-up-comm {k = 1} (scale s (ιO (ZI.ix hZ))) (valA g))
vrel-sound (comm₁ Z-gate g) = ≐-sym (emb-up-comm {k = 1} (ιO (ZI.ix zZ)) (valA g))
vrel-sound (comm₂ CZ-gate g) =
  ≐-trans (⊙-cong {M = up (up G)} {M' = upk 2 G} {N = C} {N' = C} (up-up G) (≐-refl C))
    (≐-trans (≐-sym (emb-up-comm {k = 2} (ιO (ZI.ix czZ)) G))
      (⊙-cong {M = C} {M' = C} {N = upk 2 G} {N' = up (up G)} (≐-refl C) (≐-sym (up-up G))))
  where
  G = valA g
  C = emb {2} (ιO (ZI.ix czZ))
vrel-sound (ω↑=ω neg-gate) = up-scal (- 1#)

sound : n ⊢ w ≈ v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
sound PB.refl          = ≐-refl _
sound (PB.sym e)       = ≐-sym (sound e)
sound (PB.trans e f)   = ≐-trans (sound e) (sound f)
sound (PB.cong e f)    = ⊙-cong (sound e) (sound f)
sound PB.assoc         = ⊙-assoc _ _ _
sound PB.left-unit     = ⊙-identityˡ _
sound PB.right-unit    = ⊙-identityʳ _
sound (PB.axiom r)     = vrel-sound r
