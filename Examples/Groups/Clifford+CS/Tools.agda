------------------------------------------------------------------------
-- Presentations of groups
--
-- A reasoning kit for derivations: equational reasoning on words with
-- the combinators Clément's development uses (Real-Clifford+CH's
-- TwoQubit.Conjugation.Tools), for any relation
--
-- `front`/`back`/`mid` apply an equation under a context, the
-- `cancel`/`insert`/`move` family handles an involution at either end,
-- and `unconj`/`conj-sym`/`conj-comm`/`conj-invol` are the facts about
-- conjugation by an involution.  `ax` reads a rule of Syntactics as an
-- equation of the congruence at its width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Tools where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Clifford+CS.Syntactics

------------------------------------------------------------------------
-- Tools

module Tools {X : Set} (Γ : WRel X) where
  open PB Γ public
    using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
  open PP Γ public using (word-setoid ; by-assoc)
  open PP.Pattern-Assoc Γ public using (by-passoc ; □)
  open SR word-setoid public

  front : ∀ {a b} (s : Word X) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : Word X) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  mid : ∀ (p : Word X) {a b} (s : Word X) → a ≈ b → p • a • s ≈ p • b • s
  mid p s e = cong refl (cong e refl)

  -- Cancelling an involution c (c • c ≈ ε) at either end.
  cancelˡ : ∀ {c} (s : Word X) → c • c ≈ ε → c • c • s ≈ s
  cancelˡ s e = trans (sym assoc) (trans (front s e) left-unit)

  cancelʳ : ∀ (p : Word X) {c} → c • c ≈ ε → (p • c) • c ≈ p
  cancelʳ p e = trans assoc (trans (back p e) right-unit)

  insertˡ : ∀ {c} (s : Word X) → c • c ≈ ε → s ≈ c • c • s
  insertˡ s e = sym (cancelˡ s e)

  insertʳ : ∀ (p : Word X) {c} → c • c ≈ ε → p ≈ (p • c) • c
  insertʳ p e = sym (cancelʳ p e)

  -- Moving an involution across an equation: from c • a ≈ b, a ≈ c • b.
  moveˡ : ∀ {c a b} → c • c ≈ ε → c • a ≈ b → a ≈ c • b
  moveˡ {c} {a} {b} e h = trans (insertˡ a e) (back c h)

  moveʳ : ∀ {c a b} → c • c ≈ ε → a • c ≈ b → a ≈ b • c
  moveʳ {c} {a} {b} e h = trans (insertʳ a e) (front c h)

  -- Cancelling a pair in the middle, or at the end.
  cancelᵐ : ∀ (p : Word X) {c} (s : Word X) → c • c ≈ ε → p • (c • c) • s ≈ p • s
  cancelᵐ p s e = trans (mid p s e) (back p left-unit)

  cancelᵉ : ∀ (p : Word X) {c} → c • c ≈ ε → p • (c • c) ≈ p
  cancelᵉ p e = trans (back p e) right-unit

  cancelˢ : ∀ {c} (s : Word X) → c • c ≈ ε → (c • c) • s ≈ s
  cancelˢ s e = trans (front s e) left-unit

  -- Undoing a conjugation by an involution.
  unconj : ∀ {c w} → c • c ≈ ε → c • (c • w • c) • c ≈ w
  unconj {c} {w} e = begin
    c • (c • w • c) • c
      ≈⟨ by-passoc (□ • ((□ • (□ • □)) • □)) ((□ • □) • (□ • (□ • □))) Eq.refl ⟩
    (c • c) • w • (c • c)
      ≈⟨ cong e (back _ e) ⟩
    ε • w • ε
      ≈⟨ trans left-unit right-unit ⟩
    w ∎

  -- Conjugation by an involution is symmetric, and a conjugation
  -- equation is a commutation equation.
  conj-sym : ∀ {x w w′} → x • x ≈ ε → x • w • x ≈ w′ → x • w′ • x ≈ w
  conj-sym e h = trans (mid _ _ (sym h)) (unconj e)

  conj-comm : ∀ {x w w′} → x • x ≈ ε → x • w • x ≈ w′ → w • x ≈ x • w′
  conj-comm e h = trans (insertˡ _ e) (back _ h)

  -- A conjugate of an involution is an involution.
  conj-invol : ∀ {c w} → c • c ≈ ε → w • w ≈ ε → (c • w • c) • (c • w • c) ≈ ε
  conj-invol {c} {w} e h = begin
    (c • w • c) • (c • w • c)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    c • w • (c • c) • w • c
      ≈⟨ back _ (back _ (front _ e)) ⟩
    c • w • ε • w • c
      ≈⟨ back _ (back _ left-unit) ⟩
    c • w • w • c
      ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    c • (w • w) • c
      ≈⟨ mid _ _ h ⟩
    c • ε • c
      ≈⟨ back _ left-unit ⟩
    c • c
      ≈⟨ e ⟩
    ε ∎

-- A rule of Syntactics as an equation.
ax : ∀ {k} {w v : Circuit k} → k SRel, w === v → k ⊢ w ≈ v
ax r = PB.axiom (srel r)
