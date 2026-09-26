------------------------------------------------------------------------
-- Presentations of groups
--
-- WellFormed is strictly weaker than definition 2.4
--
-- PathSum.PartialIsometry proves that definition 2.4 -- U_ξ a partial
-- isometry, U†U a projection -- implies PathSum.Isometry's WellFormed,
-- that every column of U_ξ has trace-form norm at most 1.  The
-- converse fails, and this module shows it on the smallest example:
-- the identity with its normalisation raised, idᵏ k, whose phase is 0,
-- whose outputs are its inputs, which has no path variables, and whose
-- normalisation is 1/√2^k.  Its operator is 1/√2^k times the identity.
-- Its entries are those of the identity (amp does not read k), so its
-- Gram matrix, with the normalisation cleared, is the identity rather
-- than 2^k times it:
--
--   * every column has norm 1 ≤ 2^k, so idᵏ k is WellFormed;
--   * for k ≥ 1, U†U = I/2^k is not idempotent, so idᵏ k is not a
--     partial isometry (nor an isometry): at the all-false input,
--     idempotency would say ζ^0 = 2^k · ζ^0.
--
-- ½id = idᵏ 2, a path-sum on one qubit, is the paper-sized witness
-- ½·id (WellFormed-strict).  So lemma 4.1 under WellFormed
-- (Isometry.lemma-4-1) is strictly stronger than under definition 2.4
-- (PartialIsometry.lemma-4-1-partial): ½·id satisfies its hypothesis
-- but not the other's.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _^_)

module PathSum.PartialIsometry.Strict (M₀ : ℕ) where

open import Data.Bool.Base using (true; false)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_; +≤+)
open import Data.Integer.Properties using
  (*-identityʳ; +-injective; ≤-trans; ≤-reflexive)
open import Data.Product.Base using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using (same; same-refl; same-true)
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; idPS)
open import PathSum.Cyclotomic M₀ using
  (_≐_; _·ᴬ_; zpow; coeff; coeff-map; 0ᶠ; zpow0-at-0)
open import PathSum.Denotation M₀ using (Assign; amp; amp-idPS; amp-≗)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; [_]ᴬ; Σᵃ-[]ᴬ-⊛; inner-cong; inner-basis)
open import PathSum.Isometry M₀ using
  (WellFormed; amp-no-path; idPS-diagonal)
open import PathSum.Norm M₀ using (‖_‖²; coeff-zpow0-0)
open import PathSum.PartialIsometry M₀ using
  (gram; gram-diag; Isometric; PartialIsometric;
   Isometric⇒PartialIsometric)
open import PathSum.Polynomial using (0ᴾ; μ; x[_])
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong; ·ᴬ-cong; coeff-exp)

import Data.Nat.Properties as ℕ


------------------------------------------------------------------------
-- The identity with a raised normalisation

-- Phase 0, the outputs the inputs, no path variables, and any k: the
-- operator 1/√2^k · I.  idᵏ 0 is idPS.

idᵏ : ∀ {n} k → PathSum n k 0
idᵏ k = ⟨ 0ᴾ , (λ i → μ x[ i ]) ⟩

-- amp does not read the normalisation, so the entries are those of the
-- identity: ζ^0 on the diagonal, where the single path lands, and 0
-- off it.

amp-idᵏ : ∀ {n} k (x z : Assign n) → amp (idᵏ k) x z ≐ [ same x z ]ᴬ
amp-idᵏ k x z = entry (same x z) refl
  where
  entry : ∀ b → same x z ≡ b → amp (idᵏ k) x z ≐ [ b ]ᴬ
  entry true  eq i =
    trans (amp-≗ idPS x (λ w → sym (same-true x z eq w)) i) (amp-idPS x i)
  entry false eq i = amp-no-path idPS x z (λ y → idPS-diagonal x y z) eq i

-- Hence the Gram matrix, with the normalisation cleared, is the
-- identity -- not 2^k times it.

gram-idᵏ : ∀ {n} k (x x′ : Assign n) → gram (idᵏ k) x x′ ≐ [ same x x′ ]ᴬ
gram-idᵏ k x x′ i = trans
  (inner-cong {ψ = amp (idᵏ k) x} {ψ′ = λ z → [ same x z ]ᴬ}
              {φ = amp (idᵏ k) x′} {φ′ = λ z → [ same x′ z ]ᴬ}
              (amp-idᵏ k x) (amp-idᵏ k x′) i)
  (inner-basis x x′ i)


------------------------------------------------------------------------
-- Well-formed, but not a partial isometry

-- Every column has norm 1, within the budget 2^k.

private
  coeff-[true]ᴬ : coeff [ true ]ᴬ 0ℤ ≡ 1ℤ
  coeff-[true]ᴬ = trans (coeff-exp (zpow 0ℤ) 0ℤ (+ 0) refl) coeff-zpow0-0

idᵏ-columns : ∀ {n} k (x : Assign n) →
              Σᶻ (λ z → ‖ amp (idᵏ k) x z ‖²) ≡ 1ℤ
idᵏ-columns k x = trans (sym (gram-diag (idᵏ k) x))
  (trans (coeff-map (gram-idᵏ k x x) 0ℤ)
    (trans (cong (λ b → coeff [ b ]ᴬ 0ℤ) (same-refl x)) coeff-[true]ᴬ))

idᵏ-WellFormed : ∀ {n} k → WellFormed (idᵏ {n} k)
idᵏ-WellFormed k x =
  ≤-trans (≤-reflexive (idᵏ-columns k x)) (+≤+ (ℕ.m^n>0 2 k))

-- U†U = I/2^k is not idempotent once k ≥ 1.  At the all-false input x,
-- the square of the Gram matrix is [x = x] = ζ^0, and 2^k times the
-- Gram matrix is 2^k · ζ^0; their coordinates at 0 are 1 and 2^k.

idᵏ-¬PartialIsometric : ∀ {n} k → ¬ PartialIsometric (idᵏ {n} (suc k))
idᵏ-¬PartialIsometric {n} k pi =
  contradiction (ℕ.m*n≡1⇒m≡1 2 (2 ^ k) (sym (+-injective one))) λ ()
  where
  ξ : PathSum n (suc k) 0
  ξ = idᵏ (suc k)

  x : Assign n
  x _ = false

  c : ℤ
  c = + (2 ^ suc k)

  square : Σᵃ (λ x″ → gram ξ x x″ ⊛ gram ξ x″ x) ≐ [ same x x ]ᴬ
  square i = trans
    (Σᵃ-cong (λ x″ → ⊛-cong (gram-idᵏ (suc k) x x″)
                            (gram-idᵏ (suc k) x″ x)) i)
    (Σᵃ-[]ᴬ-⊛ x x i)

  scaled : c ·ᴬ gram ξ x x ≐ c ·ᴬ [ same x x ]ᴬ
  scaled = ·ᴬ-cong c (gram-idᵏ (suc k) x x)

  at0 : [ same x x ]ᴬ 0ᶠ ≡ 1ℤ
  at0 = trans (cong (λ b → [ b ]ᴬ 0ᶠ) (same-refl x)) zpow0-at-0

  one : 1ℤ ≡ c
  one = trans (sym at0)
    (trans (sym (square 0ᶠ))
      (trans (pi x x 0ᶠ)
        (trans (scaled 0ᶠ)
          (trans (cong (c *_) at0) (*-identityʳ c)))))

idᵏ-¬Isometric : ∀ {n} k → ¬ Isometric (idᵏ {n} (suc k))
idᵏ-¬Isometric k iso =
  idᵏ-¬PartialIsometric k (Isometric⇒PartialIsometric (idᵏ (suc k)) iso)


------------------------------------------------------------------------
-- ½·id

-- The one-qubit witness: ½ · id is well-formed in PathSum.Isometry's
-- sense but not in the sense of definition 2.4.

½id : PathSum 1 2 0
½id = idᵏ 2

WellFormed-strict :
  ∃ λ (ξ : PathSum 1 2 0) → WellFormed ξ × ¬ PartialIsometric ξ
WellFormed-strict = ½id , idᵏ-WellFormed 2 , idᵏ-¬PartialIsometric 1

WellFormed⇏PartialIsometric :
  ¬ (∀ (ξ : PathSum 1 2 0) → WellFormed ξ → PartialIsometric ξ)
WellFormed⇏PartialIsometric h =
  idᵏ-¬PartialIsometric 1 (h ½id (idᵏ-WellFormed 2))
