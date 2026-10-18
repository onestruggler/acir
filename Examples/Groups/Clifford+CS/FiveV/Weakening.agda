------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation of the five-wire theory holds under one more wire on top
--
-- TopWeakening's argument, which never looks at the rules: cong↑ puts
-- an idle wire at the bottom, and the cycle σ of swaps carries w ↑ to
-- `top w` (TopWeakening.nat, in the old theory).  So it holds in the
-- theory of Five.Rules too, where the controlled rules have their
-- controls on the top wires and a rule instance with an idle wire above
-- them is not syntactically a rule instance.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.Weakening where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σ⁻¹σ ; nat ; topᵏ)
open import Examples.Groups.Clifford+CS.FiveV.Rules

private
  variable
    n : ℕ

top-congₓ : ∀ {w v : Circuit n} → n ⊢ₓ w ≈ v → (₁₊ n) ⊢ₓ top w ≈ top v
top-congₓ {n} {w} {v} e = begin
  top w                     ≈⟨ sym left-unit ⟩
  ε • top w                 ≈⟨ front _ (sym (embed (σ⁻¹σ n))) ⟩
  (σ⁻¹ n • σ n) • top w     ≈⟨ assoc ⟩
  σ⁻¹ n • (σ n • top w)     ≈⟨ back _ (sym (embed (nat w))) ⟩
  σ⁻¹ n • (w ↑ • σ n)       ≈⟨ back _ (front _ (lemma-cong↑ₓ w v e)) ⟩
  σ⁻¹ n • (v ↑ • σ n)       ≈⟨ back _ (embed (nat v)) ⟩
  σ⁻¹ n • (σ n • top v)     ≈⟨ sym assoc ⟩
  (σ⁻¹ n • σ n) • top v     ≈⟨ front _ (embed (σ⁻¹σ n)) ⟩
  ε • top v                 ≈⟨ left-unit ⟩
  top v ∎
  where open Tools ((₁₊ n) XVRel,_===_)

topᵏ-congₓ : ∀ k {w v : Circuit n} → n ⊢ₓ w ≈ v → (k + n) ⊢ₓ topᵏ k w ≈ topᵏ k v
topᵏ-congₓ zero    e = e
topᵏ-congₓ (suc k) e = top-congₓ (topᵏ-congₓ k e)
