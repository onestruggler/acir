------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of a subgroup of a presented group from completeness of
-- a smaller subgroup, a coset table and separated cosets.
--
-- An ambient presentation Γ on Z has a semantics ⟦_⟧ into some S that
-- is a homomorphism (`⟦⟧-•`) and sound, and words have right inverses.
-- Words over X and over B are read in Z (e and f).  If the words over
-- B are complete (two with the same semantics are equal), and the
-- cosets of a table for X over B — representatives rep c, and for each
-- coset and letter a fact rep c • e x ≈ f(label) • rep (next) — are
-- told apart by the semantics (`separate`), then the words over X are
-- complete (`complete`): every word is a label followed by a
-- representative (`normal`), the representatives agree by separation,
-- and the labels by the completeness of B, the representative being
-- cancelled through its inverse.  This is ThreeQubit.FiniteExtension's
-- argument with the ambient theory and its semantics abstract.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
import Presentation.Base as PB

module Presentation.CosetExtension
  {Z S : Set} (Γ : WRel Z)
  (⟦_⟧ : Word Z → S) (_∙_ : S → S → S)
  (⟦⟧-• : ∀ u v → ⟦ u • v ⟧ ≡ ⟦ u ⟧ ∙ ⟦ v ⟧)
  (sound : ∀ {u v} → PB._≈_ Γ u v → ⟦ u ⟧ ≡ ⟦ v ⟧)
  (inverse : Word Z → Word Z)
  (inverse-right : ∀ w → PB._≈_ Γ (w • inverse w) ε)
  {X B C : Set} (e : X → Word Z) (f : B → Word Z)
  (sub-complete : ∀ (l m : Word B) → ⟦ (f ʷ) l ⟧ ≡ ⟦ (f ʷ) m ⟧ →
                  PB._≈_ Γ ((f ʷ) l) ((f ʷ) m))
  (I : C) (rep : C → Word X) (rep-I : rep I ≡ ε)
  (h : C → X → Word B × C)
  (fact : ∀ c x → PB._≈_ Γ ((e ʷ) (rep c) • e x)
                           ((f ʷ) (proj₁ (h c x)) • (e ʷ) (rep (proj₂ (h c x)))))
  (separate : ∀ c c′ (l m : Word B) →
              ⟦ (f ʷ) l • (e ʷ) (rep c) ⟧ ≡ ⟦ (f ʷ) m • (e ʷ) (rep c′) ⟧ → c ≡ c′)
  where

import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

private
  E : Word X → Word Z
  E = e ʷ

  F : Word B → Word Z
  F = f ʷ

output : C → Word X → Word B
output c w = proj₁ ((h ᵗ) c w)

state : C → Word X → C
state c w = proj₂ ((h ᵗ) c w)

module _ where
  open SR (PP.word-setoid Γ)

  normal-at : ∀ c w → E (rep c) • E w ≈ F (output c w) • E (rep (state c w))
  normal-at c [ x ]ʷ = fact c x
  normal-at c ε = trans right-unit (sym left-unit)
  normal-at c (u • v) with (h ᵗ) c u | inspect ((h ᵗ) c) u
  ... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v | inspect ((h ᵗ) c′) v
  ... | (v′ , c″) | [ Eq.refl ]ᵢ = begin
    E (rep c) • (E u • E v)               ≈⟨ sym assoc ⟩
    (E (rep c) • E u) • E v               ≈⟨ cong (normal-at c u) refl ⟩
    (F u′ • E (rep c′)) • E v             ≈⟨ assoc ⟩
    F u′ • (E (rep c′) • E v)             ≈⟨ cong refl (normal-at c′ v) ⟩
    F u′ • (F v′ • E (rep c″))            ≈⟨ sym assoc ⟩
    (F u′ • F v′) • E (rep c″)            ∎

  normal : ∀ w → E w ≈ F (output I w) • E (rep (state I w))
  normal w = begin
    E w                          ≈⟨ sym left-unit ⟩
    ε • E w                      ≈⟨ cong (PB.refl' Γ (Eq.cong E (Eq.sym rep-I))) refl ⟩
    E (rep I) • E w              ≈⟨ normal-at I w ⟩
    F (output I w) • E (rep (state I w)) ∎

-- Cancelling a word on the right, semantically.
cancel : ∀ a b r → ⟦ a • r ⟧ ≡ ⟦ b • r ⟧ → ⟦ a ⟧ ≡ ⟦ b ⟧
cancel a b r eq = Eq.trans (sound (sym (un a)))
  (Eq.trans (⟦⟧-• (a • r) (inverse r))
    (Eq.trans (Eq.cong (_∙ ⟦ inverse r ⟧) eq)
      (Eq.trans (Eq.sym (⟦⟧-• (b • r) (inverse r))) (sound (un b)))))
  where
  un : ∀ x → (x • r) • inverse r ≈ x
  un x = trans assoc (trans (cong refl (inverse-right r)) right-unit)

complete : ∀ (u v : Word X) → ⟦ E u ⟧ ≡ ⟦ E v ⟧ → E u ≈ E v
complete u v eq =
  trans (normal u) (trans (cong (sub-complete (output I u) (output I v) labels)
    (PB.refl' Γ (Eq.cong (λ c → E (rep c)) states))) (sym (normal v)))
  where
  normal-eq : ⟦ F (output I u) • E (rep (state I u)) ⟧ ≡
              ⟦ F (output I v) • E (rep (state I v)) ⟧
  normal-eq = Eq.trans (sound (sym (normal u))) (Eq.trans eq (sound (normal v)))

  states : state I u ≡ state I v
  states = separate (state I u) (state I v) (output I u) (output I v) normal-eq

  labels : ⟦ F (output I u) ⟧ ≡ ⟦ F (output I v) ⟧
  labels = cancel (F (output I u)) (F (output I v)) (E (rep (state I u)))
    (Eq.trans normal-eq (Eq.cong (λ c → ⟦ F (output I v) • E (rep c) ⟧) (Eq.sym states)))
