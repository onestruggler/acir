------------------------------------------------------------------------
-- Presentations of groups
--
-- Generators beyond the pivot.
--
-- A generator g moves the basis vector e_d of its top index d (gen-col),
-- so if d lies beyond the pivot p of M, then g·M has the pivot d
-- (above), and lies above M.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Above {n : ℕ} where

open import Data.Bool.Base using (true)
open import Data.Fin.Base as Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; module ZR ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; Hᶻ ; actV-Z ; actV-X ; actV-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; pivot-just ; pivot-char ; Beyond)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (top ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀 ; ne-𝕀-at)

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
