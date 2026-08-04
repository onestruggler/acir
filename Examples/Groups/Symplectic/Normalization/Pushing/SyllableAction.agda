------------------------------------------------------------------------
-- Presentations of groups
--
-- The threaded coset action of the common composite syllables.
--
-- `_ᵗ` (Word.Base) threads `ract` left-to-right through a word, so the
-- action of a composite syllable is *definitionally* the fold of its
-- letters' actions.  This module records that fact once (`ᵗ-•`), derives
-- the decomposition combinators that let a srel-wd goal be split
-- syllable-by-syllable (`≋-cong-•`, `≋-cong-•ˡ`), and names the action
-- of each common syllable so downstream proofs can refer to it instead
-- of re-unfolding the fold.
--
-- The names here are *computations*, not closed forms: `σ-Ex c` is the
-- coset reached from c by Ex, by definition.  Proving a pattern-by-
-- pattern closed form for each is separate work; these definitions give
-- it a stable place to land.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Fin using (toℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (d-of-DS)
open import Data.Sum using (inj₂)

------------------------------------------------------------------------
-- The threaded action, and its two projections.

-- The width is explicit throughout: `C = ML` is a defined function, not
-- a datatype, so Agda cannot recover n from `C (₁₊ n)`.  (Compare the
-- `ract2 = ract {₂₊ m}` idiom in the SrelWDSel* modules.)

-- The threaded action of a whole word.
act : ∀ n → C (₁₊ n) → Circuit (₁₊ n) → Circuit n × C (₁₊ n)
act n = (ract {n} ᵗ)

-- The residual circuit emitted upward.
resid : ∀ n → C (₁₊ n) → Circuit (₁₊ n) → Circuit n
resid n c w = act n c w .proj₁

-- The coset reached.
step : ∀ n → C (₁₊ n) → Circuit (₁₊ n) → C (₁₊ n)
step n c w = act n c w .proj₂

------------------------------------------------------------------------
-- Fusion: the action of a composite word is the fold of its parts.
--
-- These hold by `refl` — `_ᵗ` is defined by exactly this recursion, and
-- the `with` on the intermediate pair reduces by eta for Σ.  Stating
-- them as lemmas lets proofs cite the decomposition instead of relying
-- on the definitional unfolding firing at the right moment.

ᵗ-ε : ∀ n (c : C (₁₊ n)) → act n c ε ≡ (ε , c)
ᵗ-ε n c = Eq.refl

ᵗ-gen : ∀ n (c : C (₁₊ n)) (g : Gen (₁₊ n)) → act n c [ g ]ʷ ≡ ract c g
ᵗ-gen n c g = Eq.refl

ᵗ-• : ∀ n (c : C (₁₊ n)) (w u : Circuit (₁₊ n)) →
  act n c (w • u) ≡
    (resid n c w • resid n (step n c w) u , step n (step n c w) u)
ᵗ-• n c w u = Eq.refl

-- The two projections of the fusion law, for rewriting in place.
resid-• : ∀ n (c : C (₁₊ n)) (w u : Circuit (₁₊ n)) →
  resid n c (w • u) ≡ resid n c w • resid n (step n c w) u
resid-• n c w u = Eq.refl

step-• : ∀ n (c : C (₁₊ n)) (w u : Circuit (₁₊ n)) →
  step n c (w • u) ≡ step n (step n c w) u
step-• n c w u = Eq.refl

------------------------------------------------------------------------
-- Decomposition combinators for ≋.
--
-- `≋` is (≈ on the residual, ≡ on the coset).  To prove two words act
-- alike it therefore suffices to match them syllable by syllable: the
-- coset component of each step feeds the next.  This is the combinator
-- a syllable-level refactor of srel-wd is built from.

module _ (n : ℕ) where
  open PB (n QRel,_===_)

  -- Split a goal at a concatenation on both sides.
  ≋-cong-• : ∀ (c : C (₁₊ n)) {w u v z : Circuit (₁₊ n)} →
    act n c w ≋ act n c v →
    act n (step n c w) u ≋ act n (step n c v) z →
    act n c (w • u) ≋ act n c (v • z)
  ≋-cong-• c (r₁ , _) (r₂ , e₂) = cong r₁ r₂ , e₂

  -- The common special case: a shared prefix.
  ≋-cong-•ˡ : ∀ (c : C (₁₊ n)) (w : Circuit (₁₊ n)) {u z : Circuit (₁₊ n)} →
    act n (step n c w) u ≋ act n (step n c w) z →
    act n c (w • u) ≋ act n c (w • z)
  ≋-cong-•ˡ c w (r , e) = cong refl r , e

  -- A shared suffix, given the prefixes agree.
  ≋-cong-•ʳ : ∀ (c : C (₁₊ n)) {w v : Circuit (₁₊ n)} (u : Circuit (₁₊ n)) →
    act n c w ≋ act n c v →
    act n c (w • u) ≋ act n c (v • u)
  ≋-cong-•ʳ c u (r , e) = cong r (refl' (Eq.cong (λ x → resid n x u) e)) ,
                          Eq.cong (λ x → step n x u) e

------------------------------------------------------------------------
-- The action of the common syllables.
--
-- For each syllable `X` we name the emitted residual `ρ-X` and the coset
-- map `σ-X`.  Widths follow Syntactics: unary syllables act on C (₁₊ n),
-- two-wire syllables on C (₂₊ n), CZ02-family on C (₃₊ n).

------------------------------------------------------------------------
-- Unary syllables (width ₁₊ n).

module _ {n : ℕ} where

  ρ-H^ : ℤ ₄ → C (₁₊ n) → Circuit n
  ρ-H^ k c = resid n c (H^ k)

  σ-H^ : ℤ ₄ → C (₁₊ n) → C (₁₊ n)
  σ-H^ k c = step n c (H^ k)

  ρ-S^ : ℤ ₚ → C (₁₊ n) → Circuit n
  ρ-S^ k c = resid n c (S^ k)

  σ-S^ : ℤ ₚ → C (₁₊ n) → C (₁₊ n)
  σ-S^ k c = step n c (S^ k)

  ρ-M : ℤ* ₚ → C (₁₊ n) → Circuit n
  ρ-M x c = resid n c (ZM x)

  σ-M : ℤ* ₚ → C (₁₊ n) → C (₁₊ n)
  σ-M x c = step n c (ZM x)

  ρ-M₁ : C (₁₊ n) → Circuit n
  ρ-M₁ c = resid n c M₁

  σ-M₁ : C (₁₊ n) → C (₁₊ n)
  σ-M₁ c = step n c M₁

------------------------------------------------------------------------
-- Two-wire syllables (width ₂₊ n).

module _ {n : ℕ} where

  ρ-Ex : C (₂₊ n) → Circuit (₁₊ n)
  ρ-Ex c = resid (₁₊ n) c Ex

  -- The coset map induced by Ex.  Ex is an involution in the group, so
  -- this is the candidate wire-swap on cosets.
  σ-Ex : C (₂₊ n) → C (₂₊ n)
  σ-Ex c = step (₁₊ n) c Ex

  ρ-CZ^ : ℤ ₚ → C (₂₊ n) → Circuit (₁₊ n)
  ρ-CZ^ k c = resid (₁₊ n) c (CZ^ k)

  σ-CZ^ : ℤ ₚ → C (₂₊ n) → C (₂₊ n)
  σ-CZ^ k c = step (₁₊ n) c (CZ^ k)

  ρ-CZ⁻¹ : C (₂₊ n) → Circuit (₁₊ n)
  ρ-CZ⁻¹ c = resid (₁₊ n) c CZ⁻¹

  σ-CZ⁻¹ : C (₂₊ n) → C (₂₊ n)
  σ-CZ⁻¹ c = step (₁₊ n) c CZ⁻¹

  ρ-CX : C (₂₊ n) → Circuit (₁₊ n)
  ρ-CX c = resid (₁₊ n) c CX

  σ-CX : C (₂₊ n) → C (₂₊ n)
  σ-CX c = step (₁₊ n) c CX

  ρ-CX' : C (₂₊ n) → Circuit (₁₊ n)
  ρ-CX' c = resid (₁₊ n) c CX'

  σ-CX' : C (₂₊ n) → C (₂₊ n)
  σ-CX' c = step (₁₊ n) c CX'

  ρ-XC : C (₂₊ n) → Circuit (₁₊ n)
  ρ-XC c = resid (₁₊ n) c XC

  σ-XC : C (₂₊ n) → C (₂₊ n)
  σ-XC c = step (₁₊ n) c XC

  ρ-XC' : C (₂₊ n) → Circuit (₁₊ n)
  ρ-XC' c = resid (₁₊ n) c XC'

  σ-XC' : C (₂₊ n) → C (₂₊ n)
  σ-XC' c = step (₁₊ n) c XC'

  ρ-CX⁻¹ : C (₂₊ n) → Circuit (₁₊ n)
  ρ-CX⁻¹ c = resid (₁₊ n) c CX⁻¹

  σ-CX⁻¹ : C (₂₊ n) → C (₂₊ n)
  σ-CX⁻¹ c = step (₁₊ n) c CX⁻¹

  ρ-XC⁻¹ : C (₂₊ n) → Circuit (₁₊ n)
  ρ-XC⁻¹ c = resid (₁₊ n) c XC⁻¹

  σ-XC⁻¹ : C (₂₊ n) → C (₂₊ n)
  σ-XC⁻¹ c = step (₁₊ n) c XC⁻¹

  ρ-CX'^ : ℤ ₚ → C (₂₊ n) → Circuit (₁₊ n)
  ρ-CX'^ k c = resid (₁₊ n) c (CX'^ k)

  σ-CX'^ : ℤ ₚ → C (₂₊ n) → C (₂₊ n)
  σ-CX'^ k c = step (₁₊ n) c (CX'^ k)

  ρ-XC^ : ℤ ₚ → C (₂₊ n) → Circuit (₁₊ n)
  ρ-XC^ k c = resid (₁₊ n) c (XC^ k)

  σ-XC^ : ℤ ₚ → C (₂₊ n) → C (₂₊ n)
  σ-XC^ k c = step (₁₊ n) c (XC^ k)

  ρ-XC'^ : ℤ ₚ → C (₂₊ n) → Circuit (₁₊ n)
  ρ-XC'^ k c = resid (₁₊ n) c (XC'^ k)

  σ-XC'^ : ℤ ₚ → C (₂₊ n) → C (₂₊ n)
  σ-XC'^ k c = step (₁₊ n) c (XC'^ k)

------------------------------------------------------------------------
-- Three-wire syllables (width ₃₊ n).

module _ {n : ℕ} where

  ρ-CZ02 : C (₃₊ n) → Circuit (₂₊ n)
  ρ-CZ02 c = resid (₂₊ n) c CZ02

  σ-CZ02 : C (₃₊ n) → C (₃₊ n)
  σ-CZ02 c = step (₂₊ n) c CZ02

  ρ-CZ02⁻¹ : C (₃₊ n) → Circuit (₂₊ n)
  ρ-CZ02⁻¹ c = resid (₂₊ n) c CZ02⁻¹

  σ-CZ02⁻¹ : C (₃₊ n) → C (₃₊ n)
  σ-CZ02⁻¹ c = step (₂₊ n) c CZ02⁻¹

  ρ-CZ02k : ℕ → C (₃₊ n) → Circuit (₂₊ n)
  ρ-CZ02k k c = resid (₂₊ n) c (CZ02k k)

  σ-CZ02k : ℕ → C (₃₊ n) → C (₃₊ n)
  σ-CZ02k k c = step (₂₊ n) c (CZ02k k)

  ρ-CZ02'k : ℕ → C (₃₊ n) → Circuit (₂₊ n)
  ρ-CZ02'k k c = resid (₂₊ n) c (CZ02'k k)

  σ-CZ02'k : ℕ → C (₃₊ n) → C (₃₊ n)
  σ-CZ02'k k c = step (₂₊ n) c (CZ02'k k)

  ρ-CZ02⁻ᵏ : ℕ → C (₃₊ n) → Circuit (₂₊ n)
  ρ-CZ02⁻ᵏ k c = resid (₂₊ n) c (CZ02⁻ᵏ k)

  σ-CZ02⁻ᵏ : ℕ → C (₃₊ n) → C (₃₊ n)
  σ-CZ02⁻ᵏ k c = step (₂₊ n) c (CZ02⁻ᵏ k)

  ρ-XC02^ : ℤ ₚ → C (₃₊ n) → Circuit (₂₊ n)
  ρ-XC02^ k c = resid (₂₊ n) c (XC02^ k)

  σ-XC02^ : ℤ ₚ → C (₃₊ n) → C (₃₊ n)
  σ-XC02^ k c = step (₂₊ n) c (XC02^ k)

  ρ-CX02^ : ℤ ₚ → C (₃₊ n) → Circuit (₂₊ n)
  ρ-CX02^ k c = resid (₂₊ n) c (CX02^ k)

  σ-CX02^ : ℤ ₚ → C (₃₊ n) → C (₃₊ n)
  σ-CX02^ k c = step (₂₊ n) c (CX02^ k)

------------------------------------------------------------------------
-- Worked example: bridging to an existing closed form.
--
-- The point of naming the actions is that a *closed form*, once proved,
-- becomes a rewrite available to every downstream proof.  S^ already has
-- one (SrelWDBase.ract-S^-coset): on an inj₂ coset, S^ k iterates the
-- D-box map d-of-DS k times and leaves the lifted tail alone.  Restated
-- in this vocabulary it reads as follows — and, being definitional, the
-- bridge is the existing lemma verbatim.
--
-- The remaining syllables need their own such theorems; that is the work
-- these definitions are a place to hang.

σ-S^-inj₂ : ∀ {m} (k : ℤ ₚ) (d : D) (lm : C (₁₊ m)) →
  σ-S^ {₁₊ m} k (inj₂ (d , lm)) ≡ inj₂ (it d-of-DS (toℕ k) d , lm)
σ-S^-inj₂ k d lm = ract-S^-coset d lm (toℕ k)
