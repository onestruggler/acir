------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma (Lemma 4.4), as the induction step on levels, and
-- completeness (Theorem 4.1).
--
-- Let M be a state at level L, and g a generator with g·M at or below
-- L.  If M = I, or g moves the basis vector e_d of an index d beyond
-- the pivot p of M, then g·M has pivot d and lies above L: this does
-- not occur.  Otherwise g acts on indices ≤ p, and the edge is a path
-- by Cases 1–3 when g is basic, and through the basic edges at L
-- (Basic) when it is not.  Subcase 3.4 is Case34, Subcase 1.14.2
-- Case1142.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.MainLemma {n : ℕ} where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; module ZR ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; lde ; num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; Hᶻ ; actV-Z ; actV-X ; actV-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-nothing ; pivot-char ; Beyond ; Lvl ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (top ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (_≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀 ; ne-𝕀-at)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (•-cancelˡ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm using (third ; levelᶜ ; levelᶜ-just ; lvlAtᶜ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n} hiding (completeness)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n} as TR
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Above {n} using (gen-col ; above)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Basic {n} using (Basic ; BasicAt ; module Conj)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 as Case1
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case2 as Case2
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case3 as Case3
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case34 as Case34
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1142 as Case1142

open PB (_===_ {n}) using (_≈_)

private
  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

------------------------------------------------------------------------
-- The induction step

-- Subcase 3.4 (Case34): the level of a state with a positive exponent
-- has the form Case34 asks for.
hyp34 : ∀ {L} (ih : EdgesBelow L) → Case3.Hyp34 {n} ih
hyp34 {L} ih s o {q} pv eq t0 t1 z01 z₁≤q le k″ eK o0 o1 r01 =
  Case34.hyp34 q k″ ℓ₁ ih₁ (Case1142.hyp1142 ih₁) s o pv (≡.trans eq L≡) t0 t1 z01 z₁≤q (≡.subst (levelᶜ (actM (H-gen _ _ z01) s) ≤ₗ_) L≡ le)
    k″ eK o0 o1 r01
  where
  ℓ₁ = third (lde (col s q)) (num (col s q))
  L₁ = suc (toℕ q) , suc k″ , ℓ₁
  L≡ : L ≡ L₁
  L≡ = ≡.trans (≡.sym eq) (≡.trans (levelᶜ-just s pv) (≡.cong (λ K → suc (toℕ q) , K , ℓ₁) eK))
  ih₁ : EdgesBelow L₁
  ih₁ = ≡.subst EdgesBelow L≡ ih

private
  -- A level with pivot index d + 1 is not at or below one with a
  -- smaller pivot index.
  not-le : ∀ {d p : ℕ} {x y} → p ℕ.< d → (suc d , x) ≤ₗ (suc p , y) → ⊥
  not-le p<d (inj₁ (inj₁ lt)) = ℕP.<-asym (s≤s p<d) lt
  not-le p<d (inj₁ (inj₂ (e , _))) = ℕP.<-irrefl (≡.sym e) (s≤s p<d)
  not-le p<d (inj₂ e) = ℕP.<-irrefl (≡.sym (≡.cong proj₁ e)) (s≤s p<d)

edge-step : EdgeStep
edge-step L ih g M o eq le = at (pivot M) ≡.refl
  where
  at : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ g ]ʷ M o
  -- M = I: g · I has the pivot top g, above (0, 0, 0).
  at nothing pv = ⊥-elim (base le′)
    where
    pv′ : pivot (actM g 𝕀) ≡ just (top g)
    pv′ = pivot-char (actM g 𝕀) (gen-col g) (Beyond-actM g {top g} {𝕀} FinP.≤-refl (λ x _ → ≡.refl))
    L≡ : L ≡ (0 , 0 , 0)
    L≡ = ≡.trans (≡.sym eq) (≡.cong (λ r → lvlAtᶜ r M) pv)
    le′ : levelᶜ (actM g 𝕀) ≤ₗ (0 , 0 , 0)
    le′ = ≡.subst₂ (λ N L′ → levelᶜ (actM g N) ≤ₗ L′) (pivot-nothing M pv) L≡ le
    base : levelᶜ (actM g 𝕀) ≤ₗ (0 , 0 , 0) → ⊥
    base l = by (≡.subst (_≤ₗ (0 , 0 , 0)) (levelᶜ-just (actM g 𝕀) pv′) l)
      where
      by : ∀ {x} → (suc (toℕ (top g)) , x) ≤ₗ (0 , 0 , 0) → ⊥
      by (inj₁ (inj₁ ()))
      by (inj₁ (inj₂ (() , _)))
      by (inj₂ ())
  at (just p) pv = dec-elim (top g FinP.≤? p) within (λ ¬tg → ⊥-elim (up (ℕP.≰⇒> ¬tg)))
    where
    k = lde (col M p)
    ℓ = third k (num (col M p))
    L≡ : L ≡ (suc (toℕ p) , k , ℓ)
    L≡ = ≡.trans (≡.sym eq) (levelᶜ-just M pv)
    -- g touches an index beyond p: the level goes up.
    up : p < top g → ⊥
    up p<d = not-le p<d (≡.subst₂ _≤ₗ_ (levelᶜ-just (actM g M) (above M pv g p<d)) L≡ le)
    L′ = suc (toℕ p) , k , ℓ
    ih′ : EdgesBelow L′
    ih′ = ≡.subst EdgesBelow L≡ ih
    h1142 = Case1142.hyp1142 ih′
    h34 = hyp34 ih′
    -- The basic edges at L′.
    basicAt : BasicAt L′
    basicAt g′ bg M′ o′ eq′ le′ = at′ (pivot M′) ≡.refl
      where
      at′ : (r : Maybe (Fin n)) → pivot M′ ≡ r → Path [ g′ ]ʷ M′ o′
      at′ nothing pv′ = ⊥-elim (ℕP.0≢1+n (≡.cong proj₁ (≡.trans (≡.sym (≡.cong (λ r → lvlAtᶜ r M′) pv′)) eq′)))
      at′ (just p′) pv′ = dec-elim (top g′ FinP.≤? p) within′ (λ ¬tg → ⊥-elim (up′ (ℕP.≰⇒> ¬tg)))
        where
        p′≡p : p′ ≡ p
        p′≡p = FinP.toℕ-injective (ℕP.suc-injective (≡.cong proj₁ (≡.trans (≡.sym (levelᶜ-just M′ pv′)) eq′)))
        pv″ : pivot M′ ≡ just p
        pv″ = ≡.trans pv′ (≡.cong just p′≡p)
        up′ : p < top g′ → ⊥
        up′ p<d = not-le p<d (≡.subst (_≤ₗ L′) (levelᶜ-just (actM g′ M′) (above M′ pv″ g′ p<d)) le′)
        within′ : top g′ ≤ p → Path [ g′ ]ʷ M′ o′
        within′ tg = by g′ bg tg le′
          where
          by : (h : Gen n) → Basic h → top h ≤ p → levelᶜ (actM h M′) ≤ₗ L′ → Path [ h ]ʷ M′ o′
          by (Z-gen j) _ tg le″ = Case2.Edge.case2 ih′ M′ o′ pv″ eq′ j tg le″
          by (X-gen a b ab) adj tg le″ = Case1.Edge.case1 ih′ h1142 M′ o′ pv″ eq′ adj tg le″
          by (H-gen a b ab) (t0 , t1) tg le″ =
            Case3.Edge.case3 ih′ M′ o′ pv″ eq′ t0 t1 tg le″ (h34 M′ o′ pv″ eq′ t0 t1 (≡.subst₂ ℕ._<_ (≡.sym t0) (≡.sym t1) (s≤s z≤n)) tg le″)
    within : top g ≤ p → Path [ g ]ʷ M o
    within tg = Conj.edge-le p k ℓ ih′ basicAt g tg M o (inj₂ (≡.trans eq L≡)) (≡.subst (levelᶜ (actM g M) ≤ₗ_) L≡ le)

-- Theorem 4.1.
completeness : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness = TR.completeness edge-step
