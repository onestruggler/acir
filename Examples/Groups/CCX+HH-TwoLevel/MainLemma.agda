------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma (Lemma 4.7) as the induction step on levels, and
-- completeness (Theorem 4.10).
--
-- An edge out of a state s at level L, not going up, given the edges
-- below L.  If s is I, every generator raises its level, and if the
-- top index of the generator lies above the pivot of s, so does it
-- (Above).  Otherwise the edge comes from the basic edges at L and the
-- edges below L (Lemma A.19: Conjugation).  The basic edges are Lemma
-- A.20: at exponent 0 they are UnitLevel's; at a positive exponent,
-- QuadM's for (-1)_[0], QuadX's for X_[x,x+1] (with QuadXE's when x is
-- the fourth odd entry and x + 1 is odd too) and QuadK's for
-- K_[0,1,2,3].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.CCX+HH-TwoLevel.MainLemma {n : ℕ} where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde ; num)
open import Examples.Groups.CCX+HH-TwoLevel.Column using (nodd ; unit-odd)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen ; _===_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM ; ⟦_⟧ᵐ)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (Lvl ; pivot ; level ; level-just)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (top)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (Bℓ)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (bℓ-below)
open import Examples.Groups.CCX+HH-TwoLevel.Above {n} using (up-just ; up-nothing)
open import Examples.Groups.CCX+HH-TwoLevel.Conjugation {n} using (Basic ; BasicAt ; module Edges)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (•-cancelˡ)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (Path ; EdgesBelow ; EdgeStep ; _≤ₗ_)
import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} as R
import Examples.Groups.CCX+HH-TwoLevel.PivotColumn as PC
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-pos)
import Examples.Groups.CCX+HH-TwoLevel.UnitLevel {n} as UnitLevel
import Examples.Groups.CCX+HH-TwoLevel.QuadM as QuadM
import Examples.Groups.CCX+HH-TwoLevel.QuadX as QuadX
import Examples.Groups.CCX+HH-TwoLevel.QuadXE as QuadXE
import Examples.Groups.CCX+HH-TwoLevel.QuadK as QuadK

open PB (_===_ {n}) using (_≈_)

private
  -- (b + 1 , 0 , 1) is at most the level of a state with pivot b: the
  -- exponent is positive, or the pivot column has an odd entry.
  bℓ-le : (q : Fin n) (k ℓ : ℕ) → (k ≡ 0 → 0 ℕ.< ℓ) → Bℓ q ≤ₗ (suc (toℕ q) , k , ℓ)
  bℓ-le q zero zero h with () ← h ≡.refl
  bℓ-le q zero (suc zero) _ = inj₂ ≡.refl
  bℓ-le q zero (suc (suc ℓ)) _ = inj₁ (inj₂ (≡.refl , inj₂ (≡.refl , ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))
  bℓ-le q (suc k) ℓ _ = inj₁ (bℓ-below {x = q} {p = q} ℓ (ℕ.s≤s ℕ.z≤n) ℕP.≤-refl)

------------------------------------------------------------------------
-- The basic edges at a level (Lemma A.20)

basicAt : ∀ L → EdgesBelow L → BasicAt L
basicAt L ih b M o B eq le = at (pivot M) ≡.refl
  where
  le′ : level (actM b M) ≤ₗ level M
  le′ = ≡.subst (level (actM b M) ≤ₗ_) (≡.sym eq) le

  ih′ : EdgesBelow (level M)
  ih′ = ≡.subst EdgesBelow (≡.sym eq) ih

  at : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ b ]ʷ M o
  at nothing pv = ⊥-elim (up-nothing b M pv le′)
  at (just q) pv = by-top (top b FinP.≤? q)
    where
    by-top : Dec (top b ≤ q) → Path [ b ]ʷ M o
    by-top (no nt) = ⊥-elim (up-just b M pv (ℕP.≰⇒> nt) le′)
    by-top (yes tb) = by-k (lde (col M q)) ≡.refl
      where
      by-k : ∀ k → lde (col M q) ≡ k → Path [ b ]ʷ M o
      by-k zero k0 = unit b B tb le′
        where
        unit : (g : Gen n) → Basic g → top g ≤ q → level (actM g M) ≤ₗ level M → Path [ g ]ʷ M o
        unit (M-gen a) a0 ta _ = UnitLevel.At.edge-M M o pv k0 ih′ a a0 ta
        unit (X-gen x y xy) adj ty _ = UnitLevel.At.edge-X M o pv k0 ih′ x y xy adj ty
        unit (K-gen a b c d ab bc cd) (a0 , b1 , c2 , d3) td lg =
          UnitLevel.At.edge-K M o pv k0 ih′ a b c d ab bc cd a0 b1 c2 d3 td lg
      by-k (suc k′) ks = quad b B tb le′
        where
        quad : (g : Gen n) → Basic g → top g ≤ q → level (actM g M) ≤ₗ level M → Path [ g ]ʷ M o
        quad (M-gen a) a0 _ _ = QuadM.edge-M M o pv ks ih′ a a0
        quad (X-gen x y xy) adj ty _ =
          QuadX.EdgeX.edge M o pv ks ih′ {x} {y} xy adj ty (QuadXE.edge-eodd M o pv ks ih′ {x} {y} xy adj ty)
        quad (K-gen a b c d ab bc cd) (a0 , b1 , c2 , d3) _ lg =
          QuadK.edge-K M o pv ks ih′ a b c d ab bc cd a0 b1 c2 d3 lg

------------------------------------------------------------------------
-- The Main Lemma: the edges at a level, given those below it

edge-step : EdgeStep
edge-step L ih g M o eq le = at (pivot M) ≡.refl
  where
  le′ : level (actM g M) ≤ₗ level M
  le′ = ≡.subst (level (actM g M) ≤ₗ_) (≡.sym eq) le

  at : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ g ]ʷ M o
  at nothing pv = ⊥-elim (up-nothing g M pv le′)
  at (just q) pv = by-top (top g FinP.≤? q)
    where
    pos : lde (col M q) ≡ 0 → 0 ℕ.< nodd (num (col M q))
    pos k0 = count-pos _ (proj₁ U) (unit-odd (proj₁ (proj₂ (proj₂ U))))
      where U = PC.unit M o pv k0

    bq : Bℓ q ≤ₗ L
    bq = ≡.subst (Bℓ q ≤ₗ_) (≡.trans (≡.sym (level-just M pv)) eq)
           (bℓ-le q (lde (col M q)) (nodd (num (col M q))) pos)

    by-top : Dec (top g ≤ q) → Path [ g ]ʷ M o
    by-top (no nt) = ⊥-elim (up-just g M pv (ℕP.≰⇒> nt) le′)
    by-top (yes tg) = Edges.edges≤ ih (basicAt L ih) bq g M o tg (inj₂ eq) le

------------------------------------------------------------------------
-- Completeness (Theorem 4.10)

completeness : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness = R.completeness edge-step •-cancelˡ
