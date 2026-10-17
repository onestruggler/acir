------------------------------------------------------------------------
-- Presentations of groups
--
-- An equation of the theory with the schema holds under one more wire
-- on top, and stretched
--
-- Five.Weakening's argument, which never looks at the rules: cong↑ puts
-- an idle wire at the bottom, and the cycle σ of swaps carries w ↑ to
-- `top w` (TopWeakening.nat, in the old theory).  Stretching (Lambda),
-- which puts the idle wire just under the top one, is a congruence and
-- a homomorphism with it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Weakening where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σ⁻¹σ ; nat ; topᵏ)
open import Examples.Groups.Clifford+CS.Lambda using (Swᵗ ; stretch)
open import Examples.Groups.Clifford+CS.Lambda.Split using (Sw² ; stretch-•)
open import Examples.Groups.Clifford+CS.Stable.Rules

private
  variable
    k n : ℕ

top-congᵧ : ∀ {w v : Circuit n} → n ⊢ᵧ w ≈ v → (₁₊ n) ⊢ᵧ top w ≈ top v
top-congᵧ {n} {w} {v} e = begin
  top w                     ≈⟨ sym left-unit ⟩
  ε • top w                 ≈⟨ front _ (sym (embed (σ⁻¹σ n))) ⟩
  (σ⁻¹ n • σ n) • top w     ≈⟨ assoc ⟩
  σ⁻¹ n • (σ n • top w)     ≈⟨ back _ (sym (embed (nat w))) ⟩
  σ⁻¹ n • (w ↑ • σ n)       ≈⟨ back _ (front _ (lemma-cong↑ᵧ w v e)) ⟩
  σ⁻¹ n • (v ↑ • σ n)       ≈⟨ back _ (embed (nat v)) ⟩
  σ⁻¹ n • (σ n • top v)     ≈⟨ sym assoc ⟩
  (σ⁻¹ n • σ n) • top v     ≈⟨ front _ (embed (σ⁻¹σ n)) ⟩
  ε • top v                 ≈⟨ left-unit ⟩
  top v ∎
  where open Tools ((₁₊ n) YVRel,_===_)

topᵏ-congᵧ : ∀ k {w v : Circuit n} → n ⊢ᵧ w ≈ v → (k + n) ⊢ᵧ topᵏ k w ≈ topᵏ k v
topᵏ-congᵧ zero    e = e
topᵏ-congᵧ (suc k) e = top-congᵧ (topᵏ-congᵧ k e)

------------------------------------------------------------------------
-- Stretching

stretch-congᵧ : ∀ {c c′ : Circuit (₂₊ k)} → (₂₊ k) ⊢ᵧ c ≈ c′ → (₃₊ k) ⊢ᵧ stretch c ≈ stretch c′
stretch-congᵧ {k} e = cong refl (cong (top-congᵧ e) refl)
  where open Tools ((₃₊ k) YVRel,_===_)

stretch-εᵧ : (₃₊ k) ⊢ᵧ stretch {k} ε ≈ ε
stretch-εᵧ {k} = trans (back _ left-unit) (embed (Sw² (suc k)))
  where open Tools ((₃₊ k) YVRel,_===_)

stretch-•ᵧ : (c c′ : Circuit (₂₊ k)) → (₃₊ k) ⊢ᵧ stretch (c • c′) ≈ stretch c • stretch c′
stretch-•ᵧ c c′ = embed (stretch-• c c′)
