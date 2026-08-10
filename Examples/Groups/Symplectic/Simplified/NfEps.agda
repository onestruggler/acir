------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.55's `nf-ε` is UNSATISFIABLE for the coset-tower normal
-- form at every positive width.
--
-- Extension.dpres asks for
--
--     inv-nf (nf ε) ≡ ε
--
-- so that the section of the identity coset is literally the empty word.
-- For the tower that cannot hold above width 0.  One level of
-- CosetNF.SingleLevel.Transfer defines its inverse as
--
--     gg (n , c) = (f ʷ) (g₁ n) • [ c ],
--
-- a concatenation whatever its arguments, and CosetTower.Extension.nfp'
-- is that same transfer.  `Word` is inductive with ε and _•_ distinct
-- constructors, so the two sides differ in head constructor and no
-- induction over the levels can close the gap.
--
-- (The width-0 case does hold: base0' sends everything to ε.)
--
-- What Extension.dpres actually needs is weaker.  nf-ε is used twice:
--
--   [I]≈ε      secᶜ Iᶜ ≈ₑ ε.  Here the congruence version is enough, and
--              free: inv-nf∘nf=id gives inv-nf (nf ε) ≈q ε, and the
--              right embedding is a congruence, so [ _ ]ᵣ ≈ₑ [ ε ]ᵣ = ε.
--   h=⁻¹f-gen  [ x ]ʷ ≈s conjss (rep Iᶜ) [ x ]ʷ.  This one genuinely
--              needs more than ≈q, because conjss recurses on the word:
--              it wants conj to respect ≈q in its acting argument, which
--              is exactly the conj-hyph hypothesis that
--              SemiDirectProduct already takes.  With it,
--              conjss (rep Iᶜ) w ≈s conjss ε w = w.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Symplectic.Simplified.NfEps
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε)

open import Examples.Groups.Symplectic.Simplified.Bijective p-2 p-prime g* g-gen
  using (nfˢ ; invˢ)

-- At width 0 the section of the identity coset is ε on the nose.
nf-ε-zero : invˢ {0} (nfˢ {0} ε) ≡ ε
nf-ε-zero = Eq.refl

-- At any positive width it is a concatenation, so the hypothesis is
-- contradictory: the absurd pattern goes through because the two sides
-- reduce to distinct constructors.
nf-ε-positive : ∀ k → invˢ {₁₊ k} (nfˢ {₁₊ k} ε) ≡ ε → ⊥
nf-ε-positive k ()
