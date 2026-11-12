------------------------------------------------------------------------
-- Presentations of groups
--
-- Lafont's Lemma 6, existence: every even permutation is the
-- denotation of a canonical form.
--
-- By induction on the width, as in the paper and in Symmetric's
-- Surjectivity.  Given an even π on ₁₊ n wires, the stairs c whose
-- target is π(0) represents π's coset: dividing ⟦ c ⟧ out of π fixes
-- wire 0 and leaves an even permutation, which with wire 0 removed is
-- the denotation of a canonical form one wire narrower.  On two wires
-- there is only the empty stairs, and there an even permutation fixes
-- wire 0, the swap being a single transposition.
--
-- This mentions no relation.  surjective packages it, for any sound
-- theory, as the surjectivity that promotes a sub-presentation to a
-- presentation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Surjectivity where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip ; lift₀
        ; lift₀-cong ; remove ; lift₀-remove ; inverseˡ ; inverseʳ )
open import Data.Nat using (ℕ)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Function.Definitions using (Surjective)
open import Notations using (₀ ; ₁ ; ₁₊ ; ₂₊)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst)
open import Word.Base using (_•_)

import Examples.Groups.Symmetric.Interpretation as SInt
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Alternating.Cosets
open import Examples.Groups.Alternating.Interpretation
open import Examples.Groups.Alternating.Normalization using (NF ; inv-nf)
open import Examples.Groups.Alternating.Parity
  using (sign ; sign-of ; sign-cong ; sign-lift₀)
open import Examples.Groups.Alternating.Semantics
open import Examples.Groups.Alternating.Syntactics
  using (Circuit ; _↑ ; Theory ; _∣_⊢_≈_)
open import Examples.Groups.Alternating.UniqueNormalForm
  using (perm-injective ; ⟦[c]⟧-zero)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The stairs of an even permutation

private
  true≢false : true ≢ false
  true≢false ()

  suc≢zero : ∀ {k} {i : Fin k} → suc i ≢ zero
  suc≢zero ()

  -- In Fin 2, what is not 1 is 0.
  not-one : (j : Fin 2) → j ≢ ₁ → j ≡ zero
  not-one zero    _  = refl
  not-one (suc zero) ne = ⊥-elim (ne refl)

-- An even permutation of two wires fixes wire 0: sending it to wire 1
-- it would be the swap, a single transposition.
fixes-zero : (a : Alt 2) → zero ≡ perm a ⟨$⟩ʳ zero
fixes-zero a = by-cases (π ⟨$⟩ʳ zero) refl
  where
  π = perm a
  by-cases : (j : Fin 2) → π ⟨$⟩ʳ zero ≡ j → zero ≡ π ⟨$⟩ʳ zero
  by-cases zero       e = sym e
  by-cases (suc zero) e =
    ⊥-elim (true≢false (trans (sym (sign-of S.σ π swap)) (even a)))
    where
    π₁ : π ⟨$⟩ʳ ₁ ≡ zero
    π₁ = not-one (π ⟨$⟩ʳ ₁) λ e′ →
           suc≢zero (perm-injective π (trans e′ (sym e)))
    swap : ∀ k → SInt.⟦ S.σ ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
    swap zero       = sym e
    swap (suc zero) = sym π₁

-- The stairs whose target is where an even permutation sends wire 0.
coset-of : (a : Alt (₁₊ n)) → ∃ λ (c : C n) → target c ≡ perm a ⟨$⟩ʳ zero
coset-of {₀}    a = ε , only (perm a ⟨$⟩ʳ zero)
  where
  only : (j : Fin 1) → zero ≡ j
  only zero = refl
coset-of {₁}    a = ε , fixes-zero a
coset-of {₂₊ m} a = coset (perm a ⟨$⟩ʳ zero) , target-coset _

------------------------------------------------------------------------
-- Every even permutation is a canonical form

canonical : ∀ n (a : Alt n) → ∃ λ (x : NF n) → ⟦ inv-nf x ⟧ ≈ᴬ a
canonical ₀      a = tt , λ ()
canonical (₁₊ n) a = (x′ , c) , correct
  where
  π = perm a
  c = proj₁ (coset-of a)
  ρ = perm ⟦ [ c ]ᶜ ⟧

  ρ₀ : ρ ⟨$⟩ʳ zero ≡ π ⟨$⟩ʳ zero
  ρ₀ = trans (⟦[c]⟧-zero c) (proj₂ (coset-of a))

  -- π with the stairs divided out fixes wire 0, and it is even.
  χ = π ∘ₚ flip ρ

  χ₀ : χ ⟨$⟩ʳ zero ≡ zero
  χ₀ = subst (λ y → ρ ⟨$⟩ˡ y ≡ zero) ρ₀ (inverseˡ ρ)

  χ-even : sign χ ≡ false
  χ-even = even (a ∙ᴬ ⟦ [ c ]ᶜ ⟧ ⁻¹ᴬ)

  -- So it is a permutation of the top wires, shifted.
  ρ′ = remove zero χ

  ρ′-even : sign ρ′ ≡ false
  ρ′-even = trans (sym (sign-lift₀ ρ′))
            (trans (sign-cong {π = lift₀ ρ′} {ρ = χ} (lift₀-remove χ χ₀))
                   χ-even)

  rec = canonical n (record { perm = ρ′ ; even = ρ′-even })
  x′  = proj₁ rec

  correct : ⟦ inv-nf x′ ↑ • [ c ]ᶜ ⟧ ≈ᴬ a
  correct k =
    trans
      (cong (ρ ⟨$⟩ʳ_)
        (trans (⟦↑⟧ (inv-nf x′) k)
        (trans (lift₀-cong (perm ⟦ inv-nf x′ ⟧) ρ′ (proj₂ rec) k)
               (lift₀-remove χ χ₀ k))))
      (inverseʳ ρ)

------------------------------------------------------------------------
-- Surjectivity of ⟦_⟧

-- The canonical form realising a, packaged as surjectivity: by
-- soundness, any circuit congruent to it denotes a.
module _ (T : Theory)
         (sound : ∀ {n} {w v : Circuit n} → T ∣ n ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧)
  where

  surjective : Surjective (_∣_⊢_≈_ T n) _≈ᴬ_ ⟦_⟧
  surjective {n} a = inv-nf x , λ z≈x k → trans (sound z≈x k) (ok k)
    where
    x  = proj₁ (canonical n a)
    ok = proj₂ (canonical n a)
