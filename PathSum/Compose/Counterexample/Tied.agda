------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 2.7 fails for definition 2.4 on tied path-sums (Amy,
-- QPL 2018)
--
-- Proposition 2.7 claims that the composite of two well-formed path-
-- sums is well formed.  PathSum.Compose.Counterexample refutes this
-- for both notions of well-formedness, but only its WellFormed
-- witnesses (plus : PathSum 1 1 1, erase : PathSum 1 0 0) have
-- definition 2.1's normalisation, 1/√2^m with m path variables.  Its
-- witnesses for definition 2.4, P₀ and P₊, are PathSum 1 2 1:
-- normalisation 1/2 with one path variable.  Read with definition
-- 2.1's normalisation 1/√2 they denote √2|0⟩⟨0| and √2|+⟩⟨+|, which
-- are not partial isometries.  So PartialIsometric-∘-fails refutes the
-- claim for PathSum.Base's path-sums, whose normalisation is free, and
-- not yet for the paper's.
--
-- The witnesses here have the tie, PathSum 1 3 3.  They are P₀ and P₊
-- with PathSum.Tied's gadget added (two more path variables, one more
-- factor 1/√2, the same operator):
--
--    P₀ᵗ = |x⟩ ↦ 1/√2³ Σ_{y₀y₁y₂} e^{2πi(⅛y₀ - ⅛y₁ + ½y₀y₁ + ½xy₂)} |x⟩
--        = |0⟩⟨0|
--    P₊ᵗ = |x⟩ ↦ 1/√2³ Σ_{y₀y₁y₂} e^{2πi(⅛y₀ - ⅛y₁ + ½y₀y₁)} |y₂⟩
--        = |+⟩⟨+|
--
-- The sum over y₀ y₁ is 1 + ζ^⅛ + ζ^-⅛ - 1 = √2, and the one over y₂ is
-- 2[x = 0] for P₀ᵗ (amp-P₀ᵗ, amp-P₊ᵗ).  Both are projections, hence
-- partial isometries.  P₀ᵗ then P₊ᵗ, the PathSum 1 6 6 that
-- PathSum.Compose's ∘ᴾ makes of them, is (1/√2)|+⟩⟨0|, which is not
-- one, although its columns still have norm at most 1
-- (PartialIsometric-∘-fails-tied, and with WellFormed
-- PartialIsometric-∘-fails-tied′; their witnesses are P₀ᵗ and P₊ᵗ by
-- definition).  So the first half of proposition 2.7 fails for
-- definition 2.4 on path-sums in the paper's own sense.
--
-- Nothing is recomputed.  tie-∘-fails takes any two path-sums
-- PathSum 1 k m with k = m + 1, given as integer matrices
-- (PathSum.Compose.Counterexample's Real) whose Gram matrices are 2^k
-- times projections while their composite's is not, and gives the
-- statement for their gadgets: real-PI and real-PI⁻ read definition
-- 2.4 off the integer matrices, gadget-≋ and ∘ᴾ-cong
-- (PathSum.Compose.Laws) relate the gadgets and their composite to the
-- originals, and definition 2.4 and WellFormed are properties of the
-- operator (PathSum.PartialIsometry's PartialIsometric-≋,
-- PathSum.Compose.WellFormed's WellFormed-≋).  Applied to P₀ and P₊ it
-- is the counterexample.
--
-- The detour through a lemma about variables is for Agda's sake.  Every
-- module opening PathSum.Denotation M₀, PathSum.PartialIsometry M₀ and
-- so on has its own copies of amp, _≋_ and PartialIsometric, and
-- indices come out spelt differently in different places (3 or suc 2);
-- where two such types meet at a closed path-sum, Agda may unfold them
-- into the closed amplitudes.  Measured: restating PartialIsometric P₀ᵗ
-- in another module cost about 70 s, P₀ᵗ ≋ P₀ about 10 s, and the
-- closed version of this module about 270 s.  At variables nothing
-- closed unfolds (this module now takes seconds), and the statements
-- exported for the root quantify over the number of path variables, so
-- restating them unfolds nothing either.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _+_)

module PathSum.Compose.Counterexample.Tied (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (zero)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _*_; _≤_; +≤+)
open import Data.Integer.Properties using
  (*-identityˡ; ≤-trans; ≤-reflexive)
open import Data.Nat.Base using (_^_; z≤n)
open import Data.Product.Base using (∃; ∃₂; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; trans)
open import Relation.Nullary.Negation using (¬_)

import Data.Nat.Properties as ℕ

open import PathSum.Base using (PathSum)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Counterexample M₀ using
  (Σ₁; gᵃ; Real; real-WF; real-PI; real-PI⁻; toY; P₀; P₊; aᵖ; a₀; a₁;
   real-toY; real-P₀; real-P₊∘P₀)
open import PathSum.Compose.Laws M₀ using (∘ᴾ-cong)
open import PathSum.Compose.WellFormed M₀ using (WellFormed-≋)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; _·ᴬ_; zpow; √2·; √2·-map)
open import PathSum.Denotation M₀ using (amp; _≋_; ≋-sym)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.PartialIsometry M₀ using
  (PartialIsometric; PartialIsometric-≋)
open import PathSum.Tied M₀ using (gadget; gadget-≋; amp-gadget; move)

private
  variable
    k m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- Moving the counterexample to the gadgets

-- Definition 2.4 for an integer matrix a: its Gram matrix is 2^k
-- times a projection (as in PathSum.Compose.Counterexample's real-PI).

Idem : ℕ → (Bool → Bool → ℤ) → Set
Idem k a =
  ∀ b b′ → Σ₁ (λ c → gᵃ a b c * gᵃ a c b′) ≡ (+ (2 ^ k)) * gᵃ a b b′

-- Two path-sums with one path variable fewer than their normalisation,
-- given by integer matrices a and b that satisfy definition 2.4 while
-- the matrix c of their composite does not, though its columns are
-- within the budget: then their gadgets are tied partial isometries
-- whose composite is not one, and is WellFormed.

tie-∘-fails :
  (ξ ζ : PathSum 1 k m) (a b c : Bool → Bool → ℤ) → k ≡ suc m →
  Real ξ a → Real ζ b → Real (ζ ∘ᴾ ξ) c →
  Idem k a → Idem k b → ¬ Idem (k + k) c →
  (∀ d → gᵃ c d d ≤ + (2 ^ (k + k))) →
  ∃ λ j → ∃₂ λ (ξ′ ζ′ : PathSum 1 j j) →
    PartialIsometric ξ′ × PartialIsometric ζ′ ×
    ¬ PartialIsometric (ζ′ ∘ᴾ ξ′) × WellFormed (ζ′ ∘ᴾ ξ′)
tie-∘-fails {m = m} ξ ζ a b c refl re rb rc ia ib ¬ic wfc =
  suc (suc m) , gadget ξ , gadget ζ ,
  PartialIsometric-≋ ξ (gadget ξ)
    (≋-sym {ξ = gadget ξ} {ζ = ξ} (gadget-≋ ξ)) (real-PI ξ a re ia) ,
  PartialIsometric-≋ ζ (gadget ζ)
    (≋-sym {ξ = gadget ζ} {ζ = ζ} (gadget-≋ ζ)) (real-PI ζ b rb ib) ,
  (λ p → ¬ic (real-PI⁻ (ζ ∘ᴾ ξ) c rc
                (PartialIsometric-≋ (gadget ζ ∘ᴾ gadget ξ) (ζ ∘ᴾ ξ) e p))) ,
  WellFormed-≋ (ζ ∘ᴾ ξ) (gadget ζ ∘ᴾ gadget ξ)
               (≋-sym {ξ = gadget ζ ∘ᴾ gadget ξ} {ζ = ζ ∘ᴾ ξ} e) wf
  where
  e : (gadget ζ ∘ᴾ gadget ξ) ≋ (ζ ∘ᴾ ξ)
  e = ∘ᴾ-cong (gadget ζ) ζ (gadget ξ) ξ (gadget-≋ ζ) (gadget-≋ ξ)

  wf : WellFormed (ζ ∘ᴾ ξ)
  wf x = ≤-trans (≤-reflexive (real-WF (ζ ∘ᴾ ξ) c rc x)) (wfc (x zero))


------------------------------------------------------------------------
-- The untied projections, as integer matrices

private
  real-P₊ : Real P₊ aᵖ
  real-P₊ = move (λ ξ → Real ξ aᵖ) (toY 2) P₊ refl (real-toY 2)

  -- P₀ and P₊ have integer Gram matrices 4 times projections ...

  idem₀ : Idem 2 a₀
  idem₀ false false = refl
  idem₀ false true  = refl
  idem₀ true  false = refl
  idem₀ true  true  = refl

  idemᵖ : Idem 2 aᵖ
  idemᵖ _ _ = refl

  -- ... and P₀ then P₊ has one that squares to 64 where 2^4 times it is
  -- 128, and columns of norm 8 and 0.

  64≢128 : + 64 ≢ + 128
  64≢128 ()

  ¬idem₁ : ¬ Idem (2 + 2) a₁
  ¬idem₁ h = 64≢128 (h false false)

  bound₁ : ∀ d → gᵃ a₁ d d ≤ + (2 ^ (2 + 2))
  bound₁ false = +≤+ (ℕ.m≤m+n 8 8)
  bound₁ true  = +≤+ z≤n


------------------------------------------------------------------------
-- The counterexample

P₀ᵗ : PathSum 1 3 3
P₀ᵗ = gadget P₀

P₊ᵗ : PathSum 1 3 3
P₊ᵗ = gadget P₊

-- Two tied partial isometries whose composite is not one, although
-- its columns still have norm at most 1.  The witnesses are P₀ᵗ and
-- P₊ᵗ (pinned by refl in PathSum.ContractTIED).

PartialIsometric-∘-fails-tied′ :
  ∃ λ m → ∃₂ λ (ξ ζ : PathSum 1 m m) →
    PartialIsometric ξ × PartialIsometric ζ ×
    ¬ PartialIsometric (ζ ∘ᴾ ξ) × WellFormed (ζ ∘ᴾ ξ)
PartialIsometric-∘-fails-tied′ =
  tie-∘-fails P₀ P₊ a₀ aᵖ a₁ refl real-P₀ real-P₊ real-P₊∘P₀
              idem₀ idemᵖ ¬idem₁ bound₁

PartialIsometric-∘-fails-tied :
  ∃ λ m → ∃₂ λ (ξ ζ : PathSum 1 m m) →
    PartialIsometric ξ × PartialIsometric ζ × ¬ PartialIsometric (ζ ∘ᴾ ξ)
PartialIsometric-∘-fails-tied = forget PartialIsometric-∘-fails-tied′
  where
  forget : (∃ λ m → ∃₂ λ (ξ ζ : PathSum 1 m m) →
              PartialIsometric ξ × PartialIsometric ζ ×
              ¬ PartialIsometric (ζ ∘ᴾ ξ) × WellFormed (ζ ∘ᴾ ξ)) →
           ∃ λ m → ∃₂ λ (ξ ζ : PathSum 1 m m) →
              PartialIsometric ξ × PartialIsometric ζ ×
              ¬ PartialIsometric (ζ ∘ᴾ ξ)
  forget (j , ξ , ζ , p , q , r , _) = j , ξ , ζ , p , q , r


------------------------------------------------------------------------
-- The tied projections' operators

-- The equations along which PathSum.Tied's facts about the gadget are
-- moved to the names.

P₀ᵗ-def : gadget P₀ ≡ P₀ᵗ
P₀ᵗ-def = refl

P₊ᵗ-def : gadget P₊ ≡ P₊ᵗ
P₊ᵗ-def = refl

-- Their entries, unnormalised: √2 times those of P₀ (2 at x = z = 0,
-- 0 elsewhere) and of P₊ (1 everywhere).  Divided by √2³ they are
-- those of |0⟩⟨0| and |+⟩⟨+|.

private
  real-amp : (ξ : PathSum 1 k m) (a : Bool → Bool → ℤ) → Real ξ a →
             ∀ x z → amp ξ x z ≐ a (x zero) (z zero) ·ᴬ zpow 0ℤ
  real-amp ξ a re = re

  amp-gadget′ : (ξ : PathSum 1 k m) →
                ∀ x z → amp (gadget ξ) x z ≐ √2· (amp ξ x z)
  amp-gadget′ = amp-gadget

amp-P₀ᵗ : ∀ x z → amp P₀ᵗ x z ≐ √2· (a₀ (x zero) (z zero) ·ᴬ zpow 0ℤ)
amp-P₀ᵗ = move (λ ξ → ∀ x z → amp ξ x z ≐
                            √2· (a₀ (x zero) (z zero) ·ᴬ zpow 0ℤ))
               (gadget P₀) P₀ᵗ P₀ᵗ-def
               (λ x z → amp-gadget′ P₀ x z
                        ∙ √2·-map (real-amp P₀ a₀ real-P₀ x z))

amp-P₊ᵗ : ∀ x z → amp P₊ᵗ x z ≐ √2· (zpow 0ℤ)
amp-P₊ᵗ = move (λ ξ → ∀ x z → amp ξ x z ≐ √2· (zpow 0ℤ))
               (gadget P₊) P₊ᵗ P₊ᵗ-def
               (λ x z → amp-gadget′ P₊ x z
                        ∙ √2·-map (real-amp P₊ aᵖ real-P₊ x z
                                   ∙ (λ i → *-identityˡ (zpow 0ℤ i))))
