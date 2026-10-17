------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor and an idle wire on top: λ¹(top w) ≈
-- stretch (λ¹ w)
--
-- A circuit with an idle top wire, put under the control, is the
-- controlled circuit with an idle wire inserted under the control.  On a
-- letter at the bottom of the domain this holds by the definition of λ¹
-- (Lambda), whose letters there are stretched from the width below; the
-- scalar's image S on the top wire is carried up by the swap
-- (`stretch-S`).  A letter one wire up has its image one wire up, so the
-- statement passes from one width to the next by cong↑ — except from a
-- four-wire domain, where the CS on the wires 1 2 and 2 3 borrow wires
-- below them (Lambda: a four-wire domain has no others), while one wire
-- up in a five-wire domain they are the CS on the wires 0 1 and 1 2
-- shifted, borrowing above.  So the statement at every width rests on
-- two equations on six wires, the joint paper's borrowed-wire switches
-- at n = 6 (scratchpad/joint/stability-notes.md: "two 6-wire facts at
-- n = 6", b6.py), which `Switch₆` takes as hypotheses:
--
--     Σ(1; 5, 2 | 3, 4) = Σ(1; 5, 2 | 0, 3),
--     Σ(2; 5, 3 | 1, 4) = Σ(2; 5, 3 | 0, 1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Coherence where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Split using (top-↑)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Weakening

private
  variable
    k m : ℕ

  module S₂ = Below 2 complete₂

------------------------------------------------------------------------
-- Stretching

-- A circuit one wire up, stretched, is the stretched circuit one wire up.
stretch-↑ : (c : Circuit (₂₊ k)) → stretch (c ↑) ≡ stretch c ↑
stretch-↑ {k} c = Eq.cong (λ x → Swᵗ (₂₊ k) • x • Swᵗ (₂₊ k)) (top-↑ c)

-- S on the top wire is carried to the new top wire.
stretch-S : ∀ k → (₃₊ k) ⊢ stretch (Sᵗ (₁₊ k)) ≈ Sᵗ (₂₊ k)
stretch-S zero    = lemma-cong↑ (Swap • S • Swap) (S ↑) (S₂.by-sem₀ (Swap • S • Swap) (S ↑) Eq.refl)
stretch-S (suc k) =
  Eq.subst (λ x → (₄₊ k) ⊢ Swᵗ (₂₊ k) • x • Swᵗ (₂₊ k) ≈ Sᵗ (₃₊ k))
           (Eq.sym (top-↑ (Sᵗ (₁₊ k))))
           (lemma-cong↑ (stretch (Sᵗ (₁₊ k))) (Sᵗ (₂₊ k)) (stretch-S k))

------------------------------------------------------------------------
-- The two equations on six wires

record Switch₆ : Set where
  field
    sw₁₂ : 6 ⊢ᵧ b-Sb2-0-41-3 ↑ ≈ stretch b-Sb0-1-42-3
    sw₂₃ : 6 ⊢ᵧ b-Sb0-1-42-3 ↑ ≈ stretch b-Sb0-2-43-1

------------------------------------------------------------------------
-- Coherence

module _ (sw : Switch₆) where
  open Switch₆ sw

  private
    -- The scalar.
    scal : ∀ m → (₂₊ (₄₊ m)) ⊢ᵧ Sᵗ (suc (₄₊ m)) ≈ stretch (Sᵗ (₄₊ m))
    scal m = PB.sym (embed (stretch-S (₃₊ m)))

    -- From one stretched letter shifted to the same, by ≡.
    shifted : (c : Circuit (₂₊ k)) → (₄₊ k) ⊢ᵧ stretch c ↑ ≈ stretch (c ↑)
    shifted c = Eq.subst (λ x → _ ⊢ᵧ stretch c ↑ ≈ x) (Eq.sym (stretch-↑ c)) PB.refl

    shifted² : (c : Circuit (₂₊ k)) → (suc (₄₊ k)) ⊢ᵧ stretch c ↑ ↑ ≈ stretch (c ↑ ↑)
    shifted² c = Eq.subst (λ x → _ ⊢ᵧ stretch c ↑ ↑ ≈ x)
                   (Eq.sym (Eq.trans (stretch-↑ (c ↑)) (Eq.cong _↑ (stretch-↑ c)))) PB.refl

    shifted³ : (c : Circuit (₂₊ k)) → (₂₊ (₄₊ k)) ⊢ᵧ stretch c ↑ ↑ ↑ ≈ stretch (c ↑ ↑ ↑)
    shifted³ c = Eq.subst (λ x → _ ⊢ᵧ stretch c ↑ ↑ ↑ ≈ x)
                   (Eq.sym (Eq.trans (stretch-↑ (c ↑ ↑))
                     (Eq.trans (Eq.cong _↑ (stretch-↑ (c ↑))) (Eq.cong (λ x → x ↑ ↑) (stretch-↑ c)))))
                   PB.refl

  λ¹-top-gen : ∀ m (g : Gen (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ᵧ λ¹ {suc m} (g ↧) ≈ stretch (λ¹ {m} g)
  λ¹-top-gen m (gate₀ I-gate)  = scal m
  λ¹-top-gen m (gate₁ S-gate)  = PB.refl
  λ¹-top-gen m (gate₁ K-gate)  = PB.refl
  λ¹-top-gen m (gate₂ CS-gate) = PB.refl
  -- One wire up, from the width below.
  λ¹-top-gen (suc m) (g ↥) =
    PB.trans (lemma-cong↑ᵧ (λ¹ (g ↧)) (stretch (λ¹ g)) (λ¹-top-gen m g)) (shifted (λ¹ g))
  -- One wire up in a four-wire domain.
  λ¹-top-gen zero (gate₀ I-gate ↥)  = scal ₀
  λ¹-top-gen zero (gate₁ S-gate ↥)  = shifted (CSᵗ ₂)
  λ¹-top-gen zero (gate₁ K-gate ↥)  = shifted (CKᵗ ₂)
  λ¹-top-gen zero (gate₂ CS-gate ↥) = sw₁₂
  λ¹-top-gen zero (gate₀ I-gate ↥ ↥)  = scal ₀
  λ¹-top-gen zero (gate₁ S-gate ↥ ↥)  = shifted² (CSᵗ ₁)
  λ¹-top-gen zero (gate₁ K-gate ↥ ↥)  = shifted² (CKᵗ ₁)
  λ¹-top-gen zero (gate₂ CS-gate ↥ ↥) = sw₂₃
  λ¹-top-gen zero (gate₀ I-gate ↥ ↥ ↥) = scal ₀
  λ¹-top-gen zero (gate₁ S-gate ↥ ↥ ↥) = shifted³ (CSᵗ ₀)
  λ¹-top-gen zero (gate₁ K-gate ↥ ↥ ↥) = shifted³ (CKᵗ ₀)
  λ¹-top-gen zero (gate₀ I-gate ↥ ↥ ↥ ↥) = scal ₀

  -- On circuits.
  λ¹-top : ∀ m (w : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ᵧ λ¹ʷ (top w) ≈ stretch (λ¹ʷ w)
  λ¹-top m [ g ]ʷ  = λ¹-top-gen m g
  λ¹-top m ε       = PB.sym stretch-εᵧ
  λ¹-top m (u • v) =
    PB.trans (PB.cong (λ¹-top m u) (λ¹-top m v)) (PB.sym (stretch-•ᵧ (λ¹ʷ u) (λ¹ʷ v)))
