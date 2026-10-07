------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for linear circuits, one wire at a time
--
-- Two normal forms W ↑ • col v • r ℓ with the same operator agree:
-- the row ℓ is the linear form written on wire 0, which neither the
-- fan-out nor anything on the upper wires changes; cancelling r ℓ,
-- the labels with wire 0 at 0 pass the fan-out unchanged, so the
-- upper parts have equal operators, hence are equal by completeness
-- one wire down; and at (1, 0, …, 0) the fan-out writes v, which the
-- upper part then determines.  Every linear circuit having a normal
-- form (Linear.Steps.decompose), two linear circuits with the same
-- operator are equal.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Soundness as Snd

module Examples.Groups.Qupit-Phase-Affine.Linear.Completeness
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ)
  (adm : Snd.Admissible p-2 p-prime lv) where

open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime lv adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Steps p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Semantics p-2 p-prime lv adm

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Evaluating a normal form

private
  -- The upper part and the fan-out keep wire 0.
  keep-head : (W : Circuit n) (v : Vec F n) (y : Labels (₁₊ n)) →
              head (fn (W ↑ • col v) y) ≡ head y
  keep-head W v (a ∷ x) = begin
    head (fn (W ↑ • col v) (a ∷ x))           ≡⟨ cong head (fn-• (W ↑) (col v) (a ∷ x)) ⟩
    head (fn (W ↑) (fn (col v) (a ∷ x)))      ≡⟨ cong (λ q → head (fn (W ↑) (proj₁ q))) (col-at v a x) ⟩
    head (fn (W ↑) (a ∷ addv a v x))          ≡⟨ cong head (fn-↑ W a (addv a v x)) ⟩
    a                                          ∎
    where open ≡-Reasoning

  -- Regrouping the normal form, the row last.
  regroup : (W : Circuit n) (v : Vec F n) (ℓ : NZ (₁₊ n)) →
            ⟦ (W ↑ • col v) • r ℓ ⟧ ≐ ⟦ ⌜ ⟨ W , v , ℓ ⟩ ⌝ ⟧
  regroup W v ℓ = sound Width.assoc

  head-nf : (W : Circuit n) (v : Vec F n) (ℓ : NZ (₁₊ n)) (x : Labels (₁₊ n)) →
            head (fn ⌜ ⟨ W , v , ℓ ⟩ ⌝ x) ≡ dot (row ℓ) x
  head-nf W v ℓ x = begin
    head (fn ⌜ ⟨ W , v , ℓ ⟩ ⌝ x)              ≡⟨ cong (λ q → head (proj₁ q)) (sym (regroup W v ℓ x)) ⟩
    head (fn ((W ↑ • col v) • r ℓ) x)          ≡⟨ cong head (fn-• (W ↑ • col v) (r ℓ) x) ⟩
    head (fn (W ↑ • col v) (fn (r ℓ) x))       ≡⟨ keep-head W v (fn (r ℓ) x) ⟩
    head (fn (r ℓ) x)                          ≡⟨ r-head ℓ x ⟩
    dot (row ℓ) x                              ∎
    where open ≡-Reasoning

  -- Wire 0 at 0: the fan-out does nothing.
  at-0 : (W : Circuit n) (v : Vec F n) (y : Labels n) →
         ⟦ W ↑ • col v ⟧ (0F ∷ y) ≡ (proj₁ (⟦ W ↑ ⟧ (0F ∷ y)) , 0F + proj₂ (⟦ W ↑ ⟧ (0F ∷ y)))
  at-0 W v y = trans (⟦⟧-• (W ↑) (col v) (0F ∷ y))
    (cong (λ q → proj₁ (⟦ W ↑ ⟧ (proj₁ q)) , proj₂ q + proj₂ (⟦ W ↑ ⟧ (proj₁ q)))
          (trans (col-at v 0F y) (cong (λ z → 0F ∷ z , 0F) (addv-0 v y))))

  -- Wire 0 at 1, the others at 0: the fan-out writes v.
  at-1 : (W : Circuit n) (v : Vec F n) → fn (W ↑ • col v) (1F ∷ 0ᵛ) ≡ 1F ∷ fn W v
  at-1 W v = begin
    fn (W ↑ • col v) (1F ∷ 0ᵛ)            ≡⟨ fn-• (W ↑) (col v) (1F ∷ 0ᵛ) ⟩
    fn (W ↑) (fn (col v) (1F ∷ 0ᵛ))       ≡⟨ cong (λ q → fn (W ↑) (proj₁ q)) (col-at v 1F 0ᵛ) ⟩
    fn (W ↑) (1F ∷ addv 1F v 0ᵛ)          ≡⟨ cong (λ z → fn (W ↑) (1F ∷ z)) (addv-1 v) ⟩
    fn (W ↑) (1F ∷ v)                     ≡⟨ fn-↑ W 1F v ⟩
    1F ∷ fn W v                           ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Equal operators, equal normal forms

private
  same-row : (W W' : Circuit n) (v v' : Vec F n) (ℓ ℓ' : NZ (₁₊ n)) →
             ⟦ ⌜ ⟨ W , v , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , v' , ℓ' ⟩ ⌝ ⟧ → r ℓ ≡ r ℓ'
  same-row W W' v v' ℓ ℓ' e = row-r ℓ ℓ' (dot-injective (row ℓ) (row ℓ') λ x →
    trans (sym (head-nf W v ℓ x)) (trans (cong (λ q → head (proj₁ q)) (e x)) (head-nf W' v' ℓ' x)))

  -- The row cancelled.
  no-row : (W W' : Circuit n) (v v' : Vec F n) (ℓ ℓ' : NZ (₁₊ n)) → r ℓ ≡ r ℓ' →
           ⟦ ⌜ ⟨ W , v , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , v' , ℓ' ⟩ ⌝ ⟧ → ⟦ W ↑ • col v ⟧ ≐ ⟦ W' ↑ • col v' ⟧
  no-row W W' v v' ℓ ℓ' er e =
    cancelʳ-⟦⟧ (W ↑ • col v) (W' ↑ • col v') (r ℓ)
      (≐-trans (regroup W v ℓ) (≐-trans e (≐-sym (subst-regroup er))))
    where
    subst-regroup : r ℓ ≡ r ℓ' → ⟦ (W' ↑ • col v') • r ℓ ⟧ ≐ ⟦ ⌜ ⟨ W' , v' , ℓ' ⟩ ⌝ ⟧
    subst-regroup er' x = trans (cong (λ q → ⟦ (W' ↑ • col v') • q ⟧ x) er') (regroup W' v' ℓ' x)

  -- The upper parts have equal operators.
  same-upper : (W W' : Circuit n) (v v' : Vec F n) →
               ⟦ W ↑ • col v ⟧ ≐ ⟦ W' ↑ • col v' ⟧ → ⟦ W ⟧ ≐ ⟦ W' ⟧
  same-upper W W' v v' e = ↑-reflect W W' 0F λ y →
    let q  = ⟦ W ↑ ⟧ (0F ∷ y)
        q' = ⟦ W' ↑ ⟧ (0F ∷ y)
        e₀ = trans (sym (at-0 W v y)) (trans (e (0F ∷ y)) (at-0 W' v' y))
    in cong₂ _,_ (cong proj₁ e₀)
         (trans (sym (FR.+-identityˡ (proj₂ q)))
           (trans (cong proj₂ e₀) (FR.+-identityˡ (proj₂ q'))))

  same-col : (W W' : Circuit n) (v v' : Vec F n) →
             ⟦ W ↑ • col v ⟧ ≐ ⟦ W' ↑ • col v' ⟧ → v ≡ v'
  same-col W W' v v' e = fn-injective W (begin
    fn W v       ≡⟨ cong tail (trans (sym (at-1 W v)) (trans (cong proj₁ (e (1F ∷ 0ᵛ))) (at-1 W' v'))) ⟩
    fn W' v'     ≡⟨ sym (cong proj₁ (same-upper W W' v v' e v')) ⟩
    fn W v'      ∎)
    where open ≡-Reasoning

nf-complete : Complete n → (N N' : LNF n) → ⟦ ⌜ N ⌝ ⟧ ≐ ⟦ ⌜ N' ⌝ ⟧ → (₁₊ n) ⊢ ⌜ N ⌝ ≈ ⌜ N' ⌝
nf-complete {n} IH ⟨ W , v , ℓ ⟩ ⟨ W' , v' , ℓ' ⟩ e = begin
  W ↑ • col v • r ℓ        ≈⟨ front _ (lift (IH (same-upper W W' v v' e₁))) ⟩
  W' ↑ • col v • r ℓ       ≈⟨ refl' (cong₂ (λ u q → W' ↑ • col u • q) (same-col W W' v v' e₁) er) ⟩
  W' ↑ • col v' • r ℓ'     ∎
  where
  open Width (₁₊ n)
  er = same-row W W' v v' ℓ ℓ' e
  e₁ = no-row W W' v v' ℓ ℓ' er e

-- Two linear circuits with the same operator are equal.
linear-complete : Complete n → (L L' : Word (LGen (₁₊ n))) →
                  ⟦ ⌊ L ⌋ ⟧ ≐ ⟦ ⌊ L' ⌋ ⟧ → (₁₊ n) ⊢ ⌊ L ⌋ ≈ ⌊ L' ⌋
linear-complete {n} IH L L' e =
  W.trans (decompose L)
    (W.trans (nf-complete IH (lnf L) (lnf L')
                (≐-trans (sound (W.sym (decompose L))) (≐-trans e (sound (decompose L')))))
             (W.sym (decompose L')))
  where module W = Width (₁₊ n)
