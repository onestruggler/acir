------------------------------------------------------------------------
-- Presentations of groups
--
-- Reversing a circuit (Clément, Appendix B.1: the mirror C† and Lemma
-- B.3, that mirroring preserves equality)
--
-- Every generator is its own inverse, so the syntactic inverse of
-- Group-Lemmas is word reversal up to the congruence, and reversal
-- preserves the congruence because inversion does.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Reverse where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊)

import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.Real-Clifford+CH.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Reversal

rev : Circuit n → Circuit n
rev [ g ]ʷ  = [ g ]ʷ
rev ε       = ε
rev (w • v) = rev v • rev w

rev-rev : (w : Circuit n) → rev (rev w) ≡ w
rev-rev [ g ]ʷ  = Eq.refl
rev-rev ε       = Eq.refl
rev-rev (w • v) = Eq.cong₂ _•_ (rev-rev w) (rev-rev v)

------------------------------------------------------------------------
-- Reversal is inversion, and preserves the congruence

-- The inverse of a generator is the generator.
private
  gen-inv : (g : Gen n) → proj₁ (grouplike g) ≡ [ g ]ʷ
  gen-inv (gate₀ ())
  gen-inv H-gen  = Eq.refl
  gen-inv Z-gen  = Eq.refl
  gen-inv CZ-gen = Eq.refl
  gen-inv CH-gen = Eq.refl
  gen-inv (g ↥) with grouplike g | gen-inv g
  ... | _ , _ | Eq.refl = Eq.refl

module _ {n : ℕ} where
  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)
  open Group-Lemmas (n VRel,_===_) grouplike using (_⁻¹ ; ⁻¹-cong)

  rev≈⁻¹ : (w : Circuit n) → rev w ≈ w ⁻¹
  rev≈⁻¹ [ g ]ʷ  = PB.refl' (n VRel,_===_) (Eq.sym (gen-inv g))
  rev≈⁻¹ ε       = refl
  rev≈⁻¹ (w • v) = cong (rev≈⁻¹ v) (rev≈⁻¹ w)

  -- Lemma B.3.
  rev-cong : {w v : Circuit n} → w ≈ v → rev w ≈ rev v
  rev-cong {w} {v} e = trans (rev≈⁻¹ w) (trans (⁻¹-cong e) (sym (rev≈⁻¹ v)))
