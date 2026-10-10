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
-- (Basic) when it is not.  Subcases 1.14.2 and 3.4 are hypotheses here
-- (Hyps), proved in Case1142 and Case34.
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
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Basic {n} using (Basic ; BasicAt ; module Conj)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 as Case1
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case2 as Case2
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case3 as Case3

open PB (_===_ {n}) using (_≈_)

private
  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

------------------------------------------------------------------------
-- A generator moves the basis vector of its top index

gen-col : (g : Gen n) → col (actM g 𝕀) (top g) ≢ col 𝕀 (top g)
gen-col (Z-gen a) =
  ne-𝕀-at (actM (Z-gen a) 𝕀) a 0 (Zᶻ a (eᶻ a)) col≡ (inj₁ ≡.refl) a
    (λ e → -1≢1 (≡.trans (≡.sym (≡.trans (set₁-a a (ZR.- (eᶻ a ! a)) (eᶻ a)) (≡.cong ZR.-_ ea))) (≡.trans e ea)))
  where
  ea : eᶻ a ! a ≡ ZR.1#
  ea = ≡.trans (eᶻ-! a a) (eδ-refl a)
  col≡ = ≡.trans (col-actM (Z-gen a) 𝕀 a) (≡.trans (≡.cong (actV (Z-gen a)) (col𝕀≡ a)) (actV-Z a 0 (eᶻ a)))
  -1≢1 : ZR.- ZR.1# ≢ ZR.1#
  -1≢1 ()
gen-col (X-gen a b ab) =
  ne-𝕀-at (actM (X-gen a b ab) 𝕀) b 0 (Xᶻ a b (eᶻ b)) col≡ (inj₁ ≡.refl) b
    (λ e → 0≢1 (≡.trans (≡.sym (≡.trans (set₂-b a b (eᶻ b ! b) (eᶻ b ! a) (eᶻ b) (<⇒≢ ab)) (≡.trans (eᶻ-! b a) (eδ-≢ (<⇒≢ ab)))))
                         (≡.trans e (≡.trans (eᶻ-! b b) (eδ-refl b)))))
  where
  col≡ = ≡.trans (col-actM (X-gen a b ab) 𝕀 b) (≡.trans (≡.cong (actV (X-gen a b ab)) (col𝕀≡ b)) (actV-X a b ab 0 (eᶻ b)))
  0≢1 : ZR.0# ≢ ZR.1#
  0≢1 ()
gen-col (H-gen a b ab) =
  ne-𝕀 (actM (H-gen a b ab) 𝕀) b 0 (Hᶻ a b (eᶻ b)) col≡ (inj₂ (a , odd-a))
  where
  col≡ = ≡.trans (col-actM (H-gen a b ab) 𝕀 b) (≡.trans (≡.cong (actV (H-gen a b ab)) (col𝕀≡ b)) (actV-H a b ab 0 (eᶻ b)))
  odd-a : oddᶻ (Hᶻ a b (eᶻ b) ! a) ≡ true
  odd-a = ≡.cong oddᶻ (≡.trans (set₂-a a b _ _ _)
            (≡.cong₂ ZR._+_ (≡.trans (eᶻ-! b a) (eδ-≢ (<⇒≢ ab))) (≡.trans (eᶻ-! b b) (eδ-refl b))))

-- Beyond the pivot, g · M has the pivot top g.
above : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (g : Gen n) → p < top g → pivot (actM g M) ≡ just (top g)
above M {p} pv g p<d = pivot-char (actM g M) ne be′
  where
  d = top g
  be = proj₂ (pivot-just M pv)
  be′ : Beyond d (actM g M)
  be′ = Beyond-actM g {d} {M} FinP.≤-refl (λ x d<x → be x (ℕP.<-trans p<d d<x))
  ne : col (actM g M) d ≢ col 𝕀 d
  ne e = gen-col g (≡.trans (col-actM g 𝕀 d) (≡.trans (≡.cong (actV g) (≡.sym (be d p<d))) (≡.trans (≡.sym (col-actM g M d)) e)))

------------------------------------------------------------------------
-- The induction step

-- Subcases 1.14.2 and 3.4, at every level.
Hyps : Set
Hyps = ∀ L (ih : EdgesBelow L) → Case1.Hyp1142 {n} ih × Case3.Hyp34 {n} ih

private
  -- A level with pivot index d + 1 is not at or below one with a
  -- smaller pivot index.
  not-le : ∀ {d p : ℕ} {x y} → p ℕ.< d → (suc d , x) ≤ₗ (suc p , y) → ⊥
  not-le p<d (inj₁ (inj₁ lt)) = ℕP.<-asym (s≤s p<d) lt
  not-le p<d (inj₁ (inj₂ (e , _))) = ℕP.<-irrefl (≡.sym e) (s≤s p<d)
  not-le p<d (inj₂ e) = ℕP.<-irrefl (≡.sym (≡.cong proj₁ e)) (s≤s p<d)

edge-step : Hyps → EdgeStep
edge-step hyps L ih g M o eq le = at (pivot M) ≡.refl
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
    h1142 = proj₁ (hyps L′ ih′)
    h34 = proj₂ (hyps L′ ih′)
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
          by (H-gen a b ab) (t0 , t1) tg le″ = Case3.Edge.case3 ih′ h34 M′ o′ pv″ eq′ t0 t1 tg le″
    within : top g ≤ p → Path [ g ]ʷ M o
    within tg = Conj.edge-le p k ℓ ih′ basicAt g tg M o (inj₂ (≡.trans eq L≡)) (≡.subst (levelᶜ (actM g M) ≤ₗ_) L≡ le)

-- Theorem 4.1, given the two subcases.
completeness-given : Hyps → {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
completeness-given hyps = completeness (edge-step hyps)
