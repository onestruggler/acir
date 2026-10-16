------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugating λ⁰ by a circuit on the domain wires
--
-- A four-wire circuit a on the bottom wires of five is λ⁰(a) λ¹(a)
-- (F5), and λ¹(a) passes λ⁰ of anything (F4), so conjugating λ⁰(G) by
-- a is λ⁰ of the four-wire conjugate (`conj⁰`).  The decoding conjugates
-- by Blake's affine circuits; for one widened from four wires, the image
-- of its syntactic inverse is the widened image of the four-wire inverse
-- (`bot-inv`), both being inverses of the same word.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)

module Examples.Groups.Clifford+CS.Five.Conj (I : Inputs) where

open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _↓ᵏ_ ; _⊢_≈_ ; grouplike)
open import Examples.Groups.Clifford+CS.Weakening using (weaken)
open import Examples.Groups.Clifford+CS.Five.Rules using (_XVRel,_===_ ; embed)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport using (transport)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ ; aff⇒)
open import Examples.Groups.Clifford+CS.Five.Bot using (bot ; τ-bot)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹ ; module Inv)

open Inputs I
open import Examples.Groups.Clifford+CS.Five.Calc F4ᵍ F5ᵍ x4x4

------------------------------------------------------------------------
-- Conjugation

private
  split : (a : Circuit 4) → a ↓ᵏ 1 ≈ Λ⁰ a • Λ¹ a
  split a = trans (sym (D-sp a)) (F5ʷ a)

conj⁰ : (a a′ G : Circuit 4) → 4 ⊢ a • a′ ≈ ε → (a ↓ᵏ 1) • Λ⁰ G • (a′ ↓ᵏ 1) ≈ Λ⁰ (a • G • a′)
conj⁰ a a′ G e = begin
  (a ↓ᵏ 1) • Λ⁰ G • (a′ ↓ᵏ 1)
    ≈⟨ cong (split a) (back (Λ⁰ G) (split a′)) ⟩
  (Λ⁰ a • Λ¹ a) • Λ⁰ G • (Λ⁰ a′ • Λ¹ a′)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • (□ • □)) Eq.refl ⟩
  Λ⁰ a • (Λ¹ a • Λ⁰ G) • (Λ⁰ a′ • Λ¹ a′)
    ≈⟨ back (Λ⁰ a) (front _ (sym (F4ʷ G a))) ⟩
  Λ⁰ a • (Λ⁰ G • Λ¹ a) • (Λ⁰ a′ • Λ¹ a′)
    ≈⟨ back (Λ⁰ a) (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl) ⟩
  Λ⁰ a • Λ⁰ G • (Λ¹ a • Λ⁰ a′) • Λ¹ a′
    ≈⟨ back (Λ⁰ a) (back (Λ⁰ G) (front _ (sym (F4ʷ a′ a)))) ⟩
  Λ⁰ a • Λ⁰ G • (Λ⁰ a′ • Λ¹ a) • Λ¹ a′
    ≈⟨ back (Λ⁰ a) (back (Λ⁰ G) assoc) ⟩
  Λ⁰ a • Λ⁰ G • Λ⁰ a′ • (Λ¹ a • Λ¹ a′)
    ≈⟨ back (Λ⁰ a) (back (Λ⁰ G) (back (Λ⁰ a′) (trans (sym (hom¹ a a′)) (transport ok e)))) ⟩
  Λ⁰ a • Λ⁰ G • Λ⁰ a′ • ε
    ≈⟨ back (Λ⁰ a) (back (Λ⁰ G) right-unit) ⟩
  Λ⁰ a • Λ⁰ G • Λ⁰ a′
    ≈⟨ back (Λ⁰ a) (sym (hom⁰ G a′)) ⟩
  Λ⁰ a • Λ⁰ (G • a′)
    ≈⟨ sym (hom⁰ a (G • a′)) ⟩
  Λ⁰ (a • G • a′) ∎

------------------------------------------------------------------------
-- The inverse of a widened affine circuit

private
  grouplikeₓ : Grouplike (_XVRel,_===_ 5)
  grouplikeₓ g = proj₁ (grouplike g) , embed (proj₂ (grouplike g))

  open module GX = Group-Lemmas (_XVRel,_===_ 5) grouplikeₓ using () renaming (_⁻¹ to _⁻ˣ ; inverseʳ-unique to unique)

bot-inv : (α : B.Circuit 4) → τ (bot α ⁻¹) ≈ τ (α ⁻¹) ↓ᵏ 1
bot-inv α = trans (unique r₁) (sym (unique r₂))
  where
  r₁ : τ (bot α) • τ (bot α ⁻¹) ≈ ε
  r₁ = embed (aff⇒ (Inv.inverseʳ 5 {bot α}))

  r₂ : τ (bot α) • (τ (α ⁻¹) ↓ᵏ 1) ≈ ε
  r₂ = Eq.subst (λ x → x • (τ (α ⁻¹) ↓ᵏ 1) ≈ ε) (Eq.sym (τ-bot α))
         (embed (weaken 1 (aff⇒ (Inv.inverseʳ 4 {α}))))
