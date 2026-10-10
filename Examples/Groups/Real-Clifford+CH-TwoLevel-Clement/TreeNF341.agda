------------------------------------------------------------------------
-- Presentations of groups
--
-- The tree of the normal form nf341 (generated).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeNF341 where

open import Data.Bool.Base using (true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([] ; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing)
open import Data.Nat.Base using (ℕ ; suc)

open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms using (Form ; form)

open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree

open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.NFs using (nfData)

private
  𝟎 𝟏 𝟐 : Z
  𝟎 = RootTwo (+ 0) (+ 0)
  𝟏 = RootTwo (+ 1) (+ 0)
  𝟐 = RootTwo (+ 2) (+ 0)
  f0 : ∀ {m} → Fin (suc m)
  f0 = zero
  f1 : ∀ {m} → Fin (suc (suc m))
  f1 = suc f0
  f2 : ∀ {m} → Fin (suc (suc (suc m)))
  f2 = suc f1
  f3 : ∀ {m} → Fin (suc (suc (suc (suc m))))
  f3 = suc f2

t341 : Tree 4 12
t341 = (leaf (l20 (f0 ∷ f1 ∷ f2 ∷ f3 ∷ []) [] false))

t341Forms : Vec (Form 12) 4
t341Forms = ((form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form 𝟏 (𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 1)) (𝟐 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ 𝟎 ∷ 𝟎 ∷ [])) ∷ (form (RootTwo (+ 1) (+ 2)) (𝟐 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 0) (+ 2)) ∷ 𝟎 ∷ 𝟎 ∷ (RootTwo (+ 4) (+ 0)) ∷ (RootTwo (+ 0) (+ 4)) ∷ [])) ∷ [])

t341Tags : Vec (Maybe ℕ) 4
t341Tags = (nothing ∷ nothing ∷ nothing ∷ nothing ∷ [])

open Checker nfData (λ _ → false) using (checkT)

t341-ok : checkT t341 t341Tags false f0 f1 t341Forms ≡ true
t341-ok = refl
