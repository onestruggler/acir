------------------------------------------------------------------------
-- Presentations of groups
--
-- Alternating groups 𝔄ₙ: Lafont's stairs as coset representatives.
--
-- A canonical form on ₁₊ n wires (Lafont, p. 268) is a canonical form
-- on the top n wires followed by a stairs, which sends wire 0 where
-- the permutation does: the stairs are representatives of the right
-- cosets of 𝔄ₙ in 𝔄ₙ₊₁, one for each target of wire 0.  A stairs of
-- size s is ω₁ ω₂ … ω_s, sending wire 0 to s, for s ≤ n − 1; the
-- last coset, wire 0 sent to n, is the stairs of size n − 1 with its
-- last cycle doubled (the fourth type of canonical form).  Here both
-- are built one wire at a time: ω•_ puts a cycle under a stairs one
-- wire up, and ωω is the doubled cycle on three wires that the last
-- stairs ends in.  (The paper's "size of the stairs" counts cycles;
-- C n describes cosets on ₁₊ n wires, and has ₁₊ n of them from n = 2
-- on.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Cosets where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ)
open import Notations using (₀ ; ₁ ; ₂ ; ₁₊ ; ₂₊ ; ₃₊)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Alternating.Syntactics
  using (Circuit ; ω ; _↑)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Coset type

infixr 10 ω•_
data C : ℕ → Set where
  ε   : C n
  ω•_ : C (₁₊ n) → C (₂₊ n)
  ωω  : C 2

------------------------------------------------------------------------
-- Section map

[_]ᶜ : C n → Circuit (₁₊ n)
[ ε    ]ᶜ = ε
[ ω• c ]ᶜ = ω • [ c ]ᶜ ↑
[ ωω   ]ᶜ = ω • ω

------------------------------------------------------------------------
-- Where a coset sends wire 0

target : C n → Fin (₁₊ n)
target ε      = zero
target (ω• c) = suc (target c)
target ωω     = ₂

target-injective : ∀ {c c′ : C n} → target c ≡ target c′ → c ≡ c′
target-injective {c = ε}      {ε}       _  = refl
target-injective {c = ω• c}   {ω• c′}   eq =
  cong ω•_ (target-injective (suc-injective eq))
target-injective {c = ωω}     {ωω}      _  = refl
target-injective {c = ε}      {ω• _}    ()
target-injective {c = ε}      {ωω}      ()
target-injective {c = ω• _}   {ε}       ()
target-injective {c = ω• ε}   {ωω}      ()
target-injective {c = ωω}     {ε}       ()
target-injective {c = ωω}     {ω• ε}    ()

-- From three wires on, every target has a coset.
coset : ∀ {m} → Fin (₃₊ m) → C (₂₊ m)
coset         ₀              = ε
coset {₀}     ₁              = ω• ε
coset {₀}     ₂              = ωω
coset {₀}     (₃₊ ())
coset {₁₊ m}  (suc j)        = ω• coset j

target-coset : ∀ {m} (j : Fin (₃₊ m)) → target (coset j) ≡ j
target-coset         ₀       = refl
target-coset {₀}     ₁       = refl
target-coset {₀}     ₂       = refl
target-coset {₀}     (₃₊ ())
target-coset {₁₊ m}  (suc j) = cong suc (target-coset j)
