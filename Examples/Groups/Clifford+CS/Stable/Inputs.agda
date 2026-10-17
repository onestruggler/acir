------------------------------------------------------------------------
-- Presentations of groups
--
-- The inputs of the gadget chain, bounded by the width
--
-- The decoding at every width (GadgetAll, Hyper, …, Lemma87) uses the
-- λ-calculus at every width: (F4) (`f4`), (F5) (`f5`) and the transport
-- one wire up (`tr`).  (F5) follows from completeness on five wires, but
-- (F4) and the transport at index m need completeness below 5 + m
-- wires, which the induction on the width has only below its target.
-- So they are given under a bound `Bnd m`, closed downwards, and every
-- statement of the chain at index m that needs them takes `Bnd m`; the
-- data (the gadgets and their decodings) take none.  With `Bnd = λ _ →
-- ⊤` (`total`) the inputs are the old ones; Stable.Theorem takes for
-- `Bnd m` completeness below 5 + m.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Inputs where

open import Data.Nat using (ℕ ; suc)
open import Data.Unit using (⊤ ; tt)

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)

-- The transport one wire up, at index m.
Tr : ℕ → Set
Tr m = ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v

record Inputs : Set₁ where
  field
    Bnd  : ℕ → Set
    down : ∀ {m} → Bnd (suc m) → Bnd m
    f4   : ∀ m → Bnd m → F4ᵗ m
    f5   : ∀ m → F5ᵗ m
    tr   : ∀ m → Bnd m → Tr m

-- The inputs with no bound.
total : (∀ m → F4ᵗ m) → (∀ m → F5ᵗ m) → (∀ m → Tr m) → Inputs
total f4 f5 tr = record
  { Bnd  = λ _ → ⊤
  ; down = λ _ → tt
  ; f4   = λ m _ → f4 m
  ; f5   = f5
  ; tr   = λ m _ → tr m
  }
