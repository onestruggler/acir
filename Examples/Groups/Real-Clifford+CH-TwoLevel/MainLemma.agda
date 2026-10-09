------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma (Lemma A.7, by Lemmas A.8 and A.9): the induction
-- step on levels, and completeness (Theorem 4.14), given the case the
-- paper's proof does not cover.
--
-- A state at level L is I (L = (0,0,0): BaseCase), or has a pivot p
-- with exponent 0 (a unit column: UnitLevel) or k > 0 (PairEdges).
-- The pair levels need, at each level, the edges H_[c,d] on two odd
-- entries of different classes when exactly four entries are odd
-- (PairEdges.Hard).  The paper derives them from its Lemma A.19,
-- whose sub-case B rests on Lemmas A.16 and A.17; these do not hold,
-- so here they are a hypothesis: completeness-given.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma {n : ℕ} where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (lde ; num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; pivot-nothing ; level ; level-just)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (•-cancelˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n}
  using (Path ; EdgesBelow ; EdgesAt ; EdgeStep ; _≤ₗ_ ; completeness)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.BaseCase {n} using (edge-𝕀)
import Examples.Groups.Real-Clifford+CH-TwoLevel.UnitLevel {n} as UnitLevel
import Examples.Groups.Real-Clifford+CH-TwoLevel.PairEdges as PairEdges

open PB (_===_ {n}) using (_≈_)

-- The hard case, at every level with a positive exponent.
Hard : Set
Hard = ∀ (p : Fin n) (k′ ℓ : ℕ) (ih : EdgesBelow (suc (toℕ p) , suc k′ , ℓ)) → PairEdges.Hard p k′ ℓ ih

-- Lemma A.7: the edges at a level, given those below it.
edge-step : Hard → EdgeStep
edge-step hard L ih g M o eq le = at (pivot M) ≡.refl
  where
  at : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ g ]ʷ M o
  at nothing pv = ≡.subst (λ N → ∀ .(o′ : ColOrth N) → Path [ g ]ʷ N o′)
                          (≡.sym (pivot-nothing M pv)) (λ _ → edge-𝕀 g) o
  at (just q) pv = by-k (lde (col M q)) ≡.refl
    where
    ℓ = nodd (num (col M q))
    by-k : ∀ k → lde (col M q) ≡ k → Path [ g ]ʷ M o
    by-k zero k0 = UnitLevel.At.edges M o pv k0 (≡.subst EdgesBelow (≡.sym eq) ih) g
    by-k (suc k′) ks = PairEdges.edgesAt q k′ ℓ ih′ (hard q k′ ℓ ih′) g M o eqM le′
      where
      eqM : level M ≡ (suc (toℕ q) , suc k′ , ℓ)
      eqM = ≡.trans (level-just M pv) (≡.cong (λ k → suc (toℕ q) , k , ℓ) ks)
      L≡ : L ≡ (suc (toℕ q) , suc k′ , ℓ)
      L≡ = ≡.trans (≡.sym eq) eqM
      ih′ : EdgesBelow (suc (toℕ q) , suc k′ , ℓ)
      ih′ = ≡.subst EdgesBelow L≡ ih
      le′ : level (actM g M) ≤ₗ (suc (toℕ q) , suc k′ , ℓ)
      le′ = ≡.subst (level (actM g M) ≤ₗ_) L≡ le

-- Theorem 4.14 (completeness), given the hard case.
completeness-given : Hard → {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness-given hard = completeness (edge-step hard) •-cancelˡ
