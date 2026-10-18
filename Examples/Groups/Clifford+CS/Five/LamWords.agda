------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus on five wires, for whole circuits
--
-- The paper's consequences of (F4) and (F5) for words: λ⁰ u and λ¹ v
-- commute for any four-wire circuits u, v (`f4ʷ`); a circuit on the
-- bottom four wires is its two halves (`splitʷ`); and conjugating λ⁰ Y
-- by a circuit c on the bottom four wires is λ⁰ of the conjugate
-- (`λ⁰-conj`): the halves λ¹ c and λ¹ c⁻¹ pass the white half and cancel
-- by transport.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.Five.Transport using (F1)

module Examples.Groups.Clifford+CS.Five.LamWords (c4 : Ws) (F : F1) where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹ ; λ⁰ʷ ; λ¹ʷ)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_ ; _XVRel,_===_)
open import Examples.Groups.Clifford+CS.Five.F4 using (f4)
open import Examples.Groups.Clifford+CS.Five.F5 using (split₅)
open import Examples.Groups.Clifford+CS.Five.Transport using (transport¹)

open Tools (5 XVRel,_===_)

------------------------------------------------------------------------
-- (F4) for words

private
  f4-gen : ∀ (g : Gen 4) (v : Circuit 4) → 5 ⊢ₓ λ⁰ g • λ¹ʷ v ≈ λ¹ʷ v • λ⁰ g
  f4-gen g [ h ]ʷ  = f4 c4 g h
  f4-gen g ε       = trans right-unit (sym left-unit)
  f4-gen g (u • v) = begin
    λ⁰ g • (λ¹ʷ u • λ¹ʷ v)   ≈⟨ sym assoc ⟩
    (λ⁰ g • λ¹ʷ u) • λ¹ʷ v   ≈⟨ front _ (f4-gen g u) ⟩
    (λ¹ʷ u • λ⁰ g) • λ¹ʷ v   ≈⟨ assoc ⟩
    λ¹ʷ u • (λ⁰ g • λ¹ʷ v)   ≈⟨ back _ (f4-gen g v) ⟩
    λ¹ʷ u • (λ¹ʷ v • λ⁰ g)   ≈⟨ sym assoc ⟩
    (λ¹ʷ u • λ¹ʷ v) • λ⁰ g ∎

f4ʷ : ∀ (u v : Circuit 4) → 5 ⊢ₓ λ⁰ʷ u • λ¹ʷ v ≈ λ¹ʷ v • λ⁰ʷ u
f4ʷ [ g ]ʷ  v = f4-gen g v
f4ʷ ε       v = trans left-unit (sym right-unit)
f4ʷ (a • b) v = begin
  (λ⁰ʷ a • λ⁰ʷ b) • λ¹ʷ v   ≈⟨ assoc ⟩
  λ⁰ʷ a • (λ⁰ʷ b • λ¹ʷ v)   ≈⟨ back _ (f4ʷ b v) ⟩
  λ⁰ʷ a • (λ¹ʷ v • λ⁰ʷ b)   ≈⟨ sym assoc ⟩
  (λ⁰ʷ a • λ¹ʷ v) • λ⁰ʷ b   ≈⟨ front _ (f4ʷ a v) ⟩
  (λ¹ʷ v • λ⁰ʷ a) • λ⁰ʷ b   ≈⟨ assoc ⟩
  λ¹ʷ v • (λ⁰ʷ a • λ⁰ʷ b) ∎

------------------------------------------------------------------------
-- (F5) for words

splitʷ : ∀ (u : Circuit 4) → 5 ⊢ₓ top u ≈ λ⁰ʷ u • λ¹ʷ u
splitʷ [ g ]ʷ  = split₅ c4 g
splitʷ ε       = sym left-unit
splitʷ (a • b) = begin
  top a • top b
    ≈⟨ cong (splitʷ a) (splitʷ b) ⟩
  (λ⁰ʷ a • λ¹ʷ a) • (λ⁰ʷ b • λ¹ʷ b)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  λ⁰ʷ a • (λ¹ʷ a • λ⁰ʷ b) • λ¹ʷ b
    ≈⟨ back _ (front _ (sym (f4ʷ b a))) ⟩
  λ⁰ʷ a • (λ⁰ʷ b • λ¹ʷ a) • λ¹ʷ b
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (λ⁰ʷ a • λ⁰ʷ b) • (λ¹ʷ a • λ¹ʷ b) ∎

------------------------------------------------------------------------
-- Conjugating the white half

λ⁰-conj : ∀ (c c⁻ Y : Circuit 4) → 4 ⊢ c • c⁻ ≈ ε →
          5 ⊢ₓ top c • λ⁰ʷ Y • top c⁻ ≈ λ⁰ʷ (c • Y • c⁻)
λ⁰-conj c c⁻ Y inv = begin
  top c • λ⁰ʷ Y • top c⁻
    ≈⟨ cong (splitʷ c) (back _ (splitʷ c⁻)) ⟩
  (λ⁰ʷ c • λ¹ʷ c) • λ⁰ʷ Y • (λ⁰ʷ c⁻ • λ¹ʷ c⁻)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • (□ • □)) • □) Eq.refl ⟩
  λ⁰ʷ c • (λ¹ʷ c • (λ⁰ʷ Y • λ⁰ʷ c⁻)) • λ¹ʷ c⁻
    ≈⟨ back _ (front _ (sym (f4ʷ (Y • c⁻) c))) ⟩
  λ⁰ʷ c • ((λ⁰ʷ Y • λ⁰ʷ c⁻) • λ¹ʷ c) • λ¹ʷ c⁻
    ≈⟨ by-passoc (□ • ((□ • □) • □) • □) ((□ • □ • □) • (□ • □)) Eq.refl ⟩
  λ⁰ʷ (c • Y • c⁻) • λ¹ʷ (c • c⁻)
    ≈⟨ back _ (transport¹ c4 F inv) ⟩
  λ⁰ʷ (c • Y • c⁻) • ε
    ≈⟨ right-unit ⟩
  λ⁰ʷ (c • Y • c⁻) ∎
