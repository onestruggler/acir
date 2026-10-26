------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor, letter by letter
--
-- λ¹ sends each generator of the four-wire domain to the word of one
-- letter of Five.Letters (`lamG`: S on the control wire for the scalar,
-- a controlled S or K for S or K, an S-box for CS), so λ¹ʷ w is the
-- letters `lamL w` (`lam-ok`, by induction on w from one flattening per
-- generator).  A controlled rule of Five.F1 is a derivation between
-- those letters (`via₀`, `via₁`), and so is a commutation of Five.F2 and
-- Five.F4 (`lam2`, `lam4`): their two sides had been compared with the
-- derivation's by flattening, tens of thousands of generators for the
-- rules with many CS (an S-box each), most of F1's checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.LamLetters where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹ ; λ¹ʷ)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Flat using (by-flat)

-- The letter of each generator's image.
lamG : Gen 4 → Mac
lamG (gate₀ I-gate)         = S4
lamG (gate₀ I-gate ↥)       = S4
lamG (gate₀ I-gate ↥ ↥)     = S4
lamG (gate₀ I-gate ↥ ↥ ↥)   = S4
lamG (gate₀ I-gate ↥ ↥ ↥ ↥) = S4
lamG (gate₁ S-gate)         = CS04
lamG (gate₁ S-gate ↥)       = CS14
lamG (gate₁ S-gate ↥ ↥)     = CS24
lamG (gate₁ S-gate ↥ ↥ ↥)   = CS34
lamG (gate₁ K-gate)         = CK40
lamG (gate₁ K-gate ↥)       = CK41
lamG (gate₁ K-gate ↥ ↥)     = CK42
lamG (gate₁ K-gate ↥ ↥ ↥)   = CK43
lamG (gate₂ CS-gate)        = Sb2-0-41-3
lamG (gate₂ CS-gate ↥)      = Sb0-1-42-3
lamG (gate₂ CS-gate ↥ ↥)    = Sb0-2-43-1

lamL : Circuit 4 → List Mac
lamL [ g ]ʷ  = lamG g ∷ []
lamL ε       = []
lamL (u • v) = lamL u ++ lamL v

-- One flattening per generator.
lamG-ok : (g : Gen 4) → 5 ⊢ₓ λ¹ʷ [ g ]ʷ ≈ ⟪ lamG g ∷ [] ⟫ʷ
lamG-ok (gate₀ I-gate)         = by-flat Eq.refl
lamG-ok (gate₀ I-gate ↥)       = by-flat Eq.refl
lamG-ok (gate₀ I-gate ↥ ↥)     = by-flat Eq.refl
lamG-ok (gate₀ I-gate ↥ ↥ ↥)   = by-flat Eq.refl
lamG-ok (gate₀ I-gate ↥ ↥ ↥ ↥) = by-flat Eq.refl
lamG-ok (gate₁ S-gate)         = by-flat Eq.refl
lamG-ok (gate₁ S-gate ↥)       = by-flat Eq.refl
lamG-ok (gate₁ S-gate ↥ ↥)     = by-flat Eq.refl
lamG-ok (gate₁ S-gate ↥ ↥ ↥)   = by-flat Eq.refl
lamG-ok (gate₁ K-gate)         = by-flat Eq.refl
lamG-ok (gate₁ K-gate ↥)       = by-flat Eq.refl
lamG-ok (gate₁ K-gate ↥ ↥)     = by-flat Eq.refl
lamG-ok (gate₁ K-gate ↥ ↥ ↥)   = by-flat Eq.refl
lamG-ok (gate₂ CS-gate)        = by-flat Eq.refl
lamG-ok (gate₂ CS-gate ↥)      = by-flat Eq.refl
lamG-ok (gate₂ CS-gate ↥ ↥)    = by-flat Eq.refl

lam-ok : (w : Circuit 4) → 5 ⊢ₓ λ¹ʷ w ≈ ⟪ lamL w ⟫ʷ
lam-ok [ g ]ʷ  = lamG-ok g
lam-ok ε       = refl
lam-ok (u • v) = trans (cong (lam-ok u) (lam-ok v)) (sym (⟪⟫-++ (lamL u) (lamL v)))

-- A controlled rule from a derivation between the letters of its sides:
-- the rule itself is an argument, so that its two words are read off
-- its type.
via₀ : ∀ {w v : Circuit 4} → 4 SRel, w === v →
       5 ⊢ₓ ⟪ lamL w ⟫ʷ ≈ ⟪ lamL v ⟫ʷ → 5 ⊢ₓ λ¹ʷ w ≈ λ¹ʷ v
via₀ {w} {v} _ e = trans (lam-ok w) (trans e (sym (lam-ok v)))

via₁ : ∀ {w v : Circuit 3} → 3 SRel, w === v →
       5 ⊢ₓ ⟪ lamL (w ↑) ⟫ʷ ≈ ⟪ lamL (v ↑) ⟫ʷ → 5 ⊢ₓ λ¹ʷ (w ↑) ≈ λ¹ʷ (v ↑)
via₁ {w} {v} _ e = trans (lam-ok (w ↑)) (trans e (sym (lam-ok (v ↑))))

-- Two controlled generators commute (Five.F2) ...
lam2 : (g h : Gen 4) →
       5 ⊢ₓ ⟪ lamG g ∷ lamG h ∷ [] ⟫ʷ ≈ ⟪ lamG h ∷ lamG g ∷ [] ⟫ʷ →
       5 ⊢ₓ λ¹ g • λ¹ h ≈ λ¹ h • λ¹ g
lam2 g h e = trans (cong (lamG-ok g) (lamG-ok h)) (trans e (sym (cong (lamG-ok h) (lamG-ok g))))

-- ... and the two halves of the controlled functor (Five.F4), λ⁰ g being
-- λ¹ g between two X on the control wire.
lam4 : (g h : Gen 4) →
       5 ⊢ₓ ⟪ X4 ∷ lamG g ∷ X4 ∷ lamG h ∷ [] ⟫ʷ ≈ ⟪ lamG h ∷ X4 ∷ lamG g ∷ X4 ∷ [] ⟫ʷ →
       5 ⊢ₓ λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g
lam4 g h e =
  trans (cong (cong refl (cong (lamG-ok g) refl)) (lamG-ok h))
    (trans assoc (trans (cong refl assoc)
      (trans e (sym (cong (lamG-ok h) (cong refl (cong (lamG-ok g) refl)))))))
