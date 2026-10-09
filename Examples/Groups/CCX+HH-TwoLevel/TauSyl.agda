------------------------------------------------------------------------
-- Presentations of groups
--
-- Signs as lists: mτ x τ is (-1)_[x] if τ and nothing otherwise, the
-- list form of Column.Mτ.  The paper's syllables carry a sign on each
-- of the four indices (K (-1)_[a]^τa (-1)_[b]^τb …); RelTau relates
-- them to the normal syllables of Column, with one sign.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.TauSyl where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; gen ; ι)

private
  variable
    m k : ℕ

mτ : Fin m → Bool → List (Gen m)
mτ x true  = M-gen x ∷ []
mτ x false = []

-- Relabelling a sign.
map-mτ : (e : Emb k m) (x : Fin k) (τ : Bool) → map (gen e) (mτ x τ) ≡ mτ (ι e x) τ
map-mτ e x true  = refl
map-mτ e x false = refl
