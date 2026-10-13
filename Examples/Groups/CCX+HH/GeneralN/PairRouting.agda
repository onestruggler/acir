------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine routing of an ordered pair of distinct basis levels.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.PairRouting where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (refl ; sym ; trans)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (_•_)
open import Examples.Groups.CCX+HH.GeneralN.Classical hiding (route)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties
  using (zeros ; e₀ ; translate ; translate-self ; act-injective ; inverse ; inverse-correct)
import Examples.Groups.CCX+HH.GeneralN.AffineRouting as A

private variable n : ℕ

record Normalize (a b : State (suc n)) : Set where
  field
    word : Circuit (suc n)
    first : act word a ≈s zeros
    second : act word b ≈s e₀

normalize : ∀ (a b : State (suc n)) → ¬ (a ≈s b) → Normalize a b
normalize {n} a b ab = record
  { word = A.Reduction.word r • tr
  ; first = λ i → trans (act-cong (A.Reduction.word r) (translate-self _ a) i)
      (A.Reduction.zero-fixed r i)
  ; second = A.Reduction.to-first r
  }
  where
  tr = translate (suc n) a
  nz : ¬ (act tr b ≈s zeros)
  nz eq = ab (act-injective tr λ i → trans (translate-self _ a i) (sym (eq i)))
  r = A.reduction (act tr b) nz

record Route (a b c d : State (suc n)) : Set where
  field
    word : Circuit (suc n)
    first : act word a ≈s c
    second : act word b ≈s d

route : ∀ (a b c d : State (suc n)) → ¬ (a ≈s b) → ¬ (c ≈s d) → Route a b c d
route a b c d ab cd = record
  { word = inverse (Normalize.word target) • Normalize.word source
  ; first = λ i → trans
      (act-cong (inverse (Normalize.word target))
        (λ j → trans (Normalize.first source j) (sym (Normalize.first target j))) i)
      (inverse-correct (Normalize.word target) c i)
  ; second = λ i → trans
      (act-cong (inverse (Normalize.word target))
        (λ j → trans (Normalize.second source j) (sym (Normalize.second target j))) i)
      (inverse-correct (Normalize.word target) d i)
  }
  where
  source = normalize a b ab
  target = normalize c d cd
