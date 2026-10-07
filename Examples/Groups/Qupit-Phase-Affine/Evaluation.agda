------------------------------------------------------------------------
-- Presentations of groups
--
-- Evaluating circuits on labels
--
-- A circuit's operator sends x to (fn w x , ph w x): the labels it
-- lands on and the phase exponent picked up on the way.  Here are the
-- equations for products and shifts, and the facts about operators
-- of circuits that come from their being invertible: a circuit
-- cancels on either side of an equation of operators, and fn w is
-- injective.  Both use soundness, so the fragment is admissible.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Soundness as Snd

module Examples.Groups.Qupit-Phase-Affine.Evaluation
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ)
  (adm : Snd.Admissible p-2 p-prime lv) where

open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (_∷_ ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv using (module Width)
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (module Inv ; _⁻¹)

open Snd p-2 p-prime lv using () renaming (sound to sound′)

private
  variable
    n : ℕ

sound : {w v : Circuit n} → n ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound = sound′ adm

------------------------------------------------------------------------
-- The labels and the phase

fn : Circuit n → Labels n → Labels n
fn w x = proj₁ (⟦ w ⟧ x)

ph : Circuit n → Labels n → F
ph w x = proj₂ (⟦ w ⟧ x)

fn-• : (w v : Circuit n) (x : Labels n) → fn (w • v) x ≡ fn w (fn v x)
fn-• w v x = Eq.cong proj₁ (⟦⟧-• w v x)

ph-• : (w v : Circuit n) (x : Labels n) → ph (w • v) x ≡ ph v x + ph w (fn v x)
ph-• w v x = Eq.cong proj₂ (⟦⟧-• w v x)

fn-ε : (x : Labels n) → fn ε x ≡ x
fn-ε x = Eq.cong proj₁ (⟦⟧-ε x)

ph-ε : (x : Labels n) → ph ε x ≡ 0F
ph-ε x = Eq.cong proj₂ (⟦⟧-ε x)

fn-↑ : (w : Circuit n) (a : F) (x : Labels n) → fn (w ↑) (a ∷ x) ≡ a ∷ fn w x
fn-↑ w a x = Eq.cong proj₁ (up-word w (a ∷ x))

ph-↑ : (w : Circuit n) (a : F) (x : Labels n) → ph (w ↑) (a ∷ x) ≡ ph w x
ph-↑ w a x = Eq.cong proj₂ (up-word w (a ∷ x))

------------------------------------------------------------------------
-- Equal circuits evaluate alike

fn-≈ : {w v : Circuit n} → n ⊢ w ≈ v → (x : Labels n) → fn w x ≡ fn v x
fn-≈ e x = Eq.cong proj₁ (sound e x)

ph-≈ : {w v : Circuit n} → n ⊢ w ≈ v → (x : Labels n) → ph w x ≡ ph v x
ph-≈ e x = Eq.cong proj₂ (sound e x)

------------------------------------------------------------------------
-- Circuits are invertible

-- The inverse undoes the labels.
fn-⁻¹ : (w : Circuit n) (x : Labels n) → fn (w ⁻¹) (fn w x) ≡ x
fn-⁻¹ {n} w x = Eq.trans (Eq.sym (fn-• (w ⁻¹) w x))
                         (Eq.trans (fn-≈ (Inv.inverseˡ n) x) (fn-ε x))

fn-injective : (w : Circuit n) {x y : Labels n} → fn w x ≡ fn w y → x ≡ y
fn-injective w {x} {y} e =
  Eq.trans (Eq.sym (fn-⁻¹ w x)) (Eq.trans (Eq.cong (fn (w ⁻¹)) e) (fn-⁻¹ w y))

-- A circuit cancels on the right of an equation of operators.
cancelʳ-⟦⟧ : (u v c : Circuit n) → ⟦ u • c ⟧ ≐ ⟦ v • c ⟧ → ⟦ u ⟧ ≐ ⟦ v ⟧
cancelʳ-⟦⟧ {n} u v c e =
  ≐-trans (sound (sym (undo u)))
    (≐-trans (⟦⟧-• (u • c) (c ⁻¹))
      (≐-trans (⊙-cong e (≐-refl ⟦ c ⁻¹ ⟧))
        (≐-trans (≐-sym (⟦⟧-• (v • c) (c ⁻¹))) (sound (undo v)))))
  where
  open Width n
  undo : (t : Circuit n) → n ⊢ (t • c) • c ⁻¹ ≈ t
  undo t = trans assoc (trans (back t (Inv.inverseʳ n)) right-unit)

-- And on the left.
cancelˡ-⟦⟧ : (c u v : Circuit n) → ⟦ c • u ⟧ ≐ ⟦ c • v ⟧ → ⟦ u ⟧ ≐ ⟦ v ⟧
cancelˡ-⟦⟧ {n} c u v e =
  ≐-trans (sound (sym (undo u)))
    (≐-trans (⟦⟧-• (c ⁻¹) (c • u))
      (≐-trans (⊙-cong (≐-refl ⟦ c ⁻¹ ⟧) e)
        (≐-trans (≐-sym (⟦⟧-• (c ⁻¹) (c • v))) (sound (undo v)))))
  where
  open Width n
  undo : (t : Circuit n) → n ⊢ c ⁻¹ • c • t ≈ t
  undo t = trans (sym assoc) (trans (front t (Inv.inverseˡ n)) left-unit)

-- Equal operators one wire up, read on the labels with wire 0 at a,
-- are equal operators.
↑-reflect : (w v : Circuit n) (a : F) → (∀ x → ⟦ w ↑ ⟧ (a ∷ x) ≡ ⟦ v ↑ ⟧ (a ∷ x)) → ⟦ w ⟧ ≐ ⟦ v ⟧
↑-reflect w v a e x = Eq.cong₂ _,_ fx px
  where
  fx : fn w x ≡ fn v x
  fx = Eq.cong tail
         (Eq.trans (Eq.sym (fn-↑ w a x)) (Eq.trans (Eq.cong proj₁ (e x)) (fn-↑ v a x)))
  px : ph w x ≡ ph v x
  px = Eq.trans (Eq.sym (ph-↑ w a x)) (Eq.trans (Eq.cong proj₂ (e x)) (ph-↑ v a x))

------------------------------------------------------------------------
-- Completeness at a width

Complete : ℕ → Set
Complete n = ∀ {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → n ⊢ w ≈ v
