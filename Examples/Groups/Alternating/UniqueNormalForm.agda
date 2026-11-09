------------------------------------------------------------------------
-- Presentations of groups
--
-- Lafont's Lemma 6, uniqueness: two canonical forms that denote the
-- same permutation are the same.
--
-- By induction on the width, as in the paper.  The stairs of a
-- canonical form is determined by where the permutation sends wire 0,
-- the canonical form on the top wires leaving wire 0 alone; cancelling
-- the stairs (a bijection) leaves two shifted canonical forms with the
-- same denotation, hence (suc-injective) two canonical forms one wire
-- narrower with the same denotation.  This mentions no relation; it is
-- packaged as a UniqueNormalForm for a theory in Completeness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.UniqueNormalForm where

open import Data.Fin using (zero ; suc)
open import Data.Fin.Permutation
  using (Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; inverseˡ)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Notations using (₀ ; ₁ ; ₁₊)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import Examples.Groups.Alternating.Cosets
open import Examples.Groups.Alternating.Interpretation
open import Examples.Groups.Alternating.Normalization using (NF ; inv-nf)
open import Examples.Groups.Alternating.Semantics
open import Examples.Groups.Alternating.Syntactics using (_↑)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The stairs of a canonical form

-- A permutation is injective.
perm-injective : (π : Permutation′ n) {i j : _} →
                 π ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ j → i ≡ j
perm-injective π {i} {j} eq =
  trans (sym (inverseˡ π)) (trans (cong (π ⟨$⟩ˡ_) eq) (inverseˡ π))

-- A stairs sends wire 0 to its target.
⟦[c]⟧-zero : (c : C n) → perm ⟦ [ c ]ᶜ ⟧ ⟨$⟩ʳ zero ≡ target c
⟦[c]⟧-zero ε      = refl
⟦[c]⟧-zero (ω• c) = trans (⟦↑⟧ [ c ]ᶜ ₁) (cong suc (⟦[c]⟧-zero c))
⟦[c]⟧-zero ωω     = refl

------------------------------------------------------------------------
-- Uniqueness

inv-nf-injective : ∀ {u v : NF n} → ⟦ inv-nf u ⟧ ≈ᴬ ⟦ inv-nf v ⟧ → u ≡ v
inv-nf-injective {₀}    {tt}    {tt}     _  = refl
inv-nf-injective {₁₊ n} {x , c} {x′ , c′} eq = cong₂ _,_ x≡x′ c≡c′
  where
  open ≡-Reasoning
  ρ  = perm ⟦ [ c ]ᶜ ⟧
  ρ′ = perm ⟦ [ c′ ]ᶜ ⟧

  -- The stairs: compare where wire 0 goes.
  c≡c′ : c ≡ c′
  c≡c′ = target-injective (begin
    target c                                   ≡⟨ sym (⟦[c]⟧-zero c) ⟩
    ρ ⟨$⟩ʳ zero                                ≡⟨ cong (ρ ⟨$⟩ʳ_)
                                                    (⟦↑⟧ (inv-nf x) zero) ⟨
    ρ ⟨$⟩ʳ (perm ⟦ inv-nf x ↑ ⟧ ⟨$⟩ʳ zero)      ≡⟨ eq zero ⟩
    ρ′ ⟨$⟩ʳ (perm ⟦ inv-nf x′ ↑ ⟧ ⟨$⟩ʳ zero)    ≡⟨ cong (ρ′ ⟨$⟩ʳ_)
                                                    (⟦↑⟧ (inv-nf x′) zero) ⟩
    ρ′ ⟨$⟩ʳ zero                               ≡⟨ ⟦[c]⟧-zero c′ ⟩
    target c′                                  ∎)

  -- The rest: cancel the stairs, then the shift.
  x≡x′ : x ≡ x′
  x≡x′ = inv-nf-injective {n} same
    where
    same : ⟦ inv-nf x ⟧ ≈ᴬ ⟦ inv-nf x′ ⟧
    same j = suc-injective (begin
      suc (perm ⟦ inv-nf x ⟧ ⟨$⟩ʳ j)     ≡⟨ ⟦↑⟧ (inv-nf x) (suc j) ⟨
      perm ⟦ inv-nf x ↑ ⟧ ⟨$⟩ʳ suc j     ≡⟨ perm-injective ρ
                                              (trans (eq (suc j)) on-c) ⟩
      perm ⟦ inv-nf x′ ↑ ⟧ ⟨$⟩ʳ suc j    ≡⟨ ⟦↑⟧ (inv-nf x′) (suc j) ⟩
      suc (perm ⟦ inv-nf x′ ⟧ ⟨$⟩ʳ j)    ∎)
      where
      -- The two stairs are the same.
      on-c : ρ′ ⟨$⟩ʳ (perm ⟦ inv-nf x′ ↑ ⟧ ⟨$⟩ʳ suc j) ≡
             ρ ⟨$⟩ʳ (perm ⟦ inv-nf x′ ↑ ⟧ ⟨$⟩ʳ suc j)
      on-c = cong (λ d → perm ⟦ [ d ]ᶜ ⟧ ⟨$⟩ʳ
                           (perm ⟦ inv-nf x′ ↑ ⟧ ⟨$⟩ʳ suc j))
                  (sym c≡c′)
