------------------------------------------------------------------------
-- Presentations of groups
--
-- Five ordered fresh basis levels outside a four-level support.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.FiveFreshLevels where

open import Data.Fin.Base using (Fin ; _<_ ; _↑ˡ_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; _+_ ; _≤_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ ; _,_)
open import Data.Vec.Base using (Vec ; lookup)
open import Relation.Binary.PropositionalEquality
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)
open import Examples.Groups.CCX+H.GeneralN.SpareLevels using (complement ; module Complement)

record Five {n : ℕ} (xs : Vec (Fin n) 4) : Set where
  field
    levels : Emb 5 n
    outside : ∀ i j → ι levels i ≢ lookup xs j

five : ∀ {n} (xs : Vec (Fin n) 4) → 9 ≤ n → Five xs
five {n} xs bound = choose (NP.m≤n⇒∃[o]m+o≡n bound)
  where
  build : ∀ m {n} → 9 + m ≡ n → (ys : Vec (Fin n) 4) → Five ys
  build m refl ys = record
    { levels = record { ι = λ i → C.embed (i ↑ˡ m) ; mono = increasing }
    ; outside = λ i → C.outside (i ↑ˡ m)
    }
    where
    module C = Complement (complement ys)
    increasing : ∀ {i j : Fin 5} → i < j → C.embed (i ↑ˡ m) < C.embed (j ↑ˡ m)
    increasing {i} {j} ij = C.increasing (i ↑ˡ m) (j ↑ˡ m) lifted
      where
      lifted : (i ↑ˡ m) < (j ↑ˡ m)
      lifted rewrite FP.toℕ-↑ˡ i m | FP.toℕ-↑ˡ j m = ij
  choose : (Σ ℕ λ m → 9 + m ≡ n) → Five xs
  choose (m , eq) = build m eq xs
