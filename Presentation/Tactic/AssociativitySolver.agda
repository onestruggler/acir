------------------------------------------------------------------------
-- Presentations of groups
--
-- An associativity solver for the congruence ≈ of a presentation.
--
-- to-list flattens a word to its list of generators (dropping the
-- bracketing and units); by-assoc then proves w ≈ v by comparing the
-- flattened lists (typically by refl).  Pattern-Assoc is the
-- pattern-guided variant: special-assoc re-brackets guided by pattern
-- words built from □.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base

module Presentation.Tactic.AssociativitySolver {X : Set} (Γ : WRel X) where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Unit using (⊤ ; tt)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid ; IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.Base Γ

-- The setoid of words modulo ≈, used for the equational-reasoning
-- proofs below.  (Kept local to avoid a dependency cycle with
-- Presentation.Properties, which re-exports this module.)
private
  word-setoid : Setoid 0ℓ 0ℓ
  word-setoid = record
    { Carrier       = Word X
    ; _≈_           = _≈_
    ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    }

------------------------------------------------------------------------
-- Flatten a word to its list of generators, and back

to-list : ∀ {X} → Word X → List X
to-list [ x ]ʷ  = x ∷ []
to-list ε        = []
to-list (w • w₁) = to-list w ++ to-list w₁

from-list : ∀ {X} → List X → Word X
from-list []       = ε
from-list (x ∷ xs) = [ x ]ʷ • from-list xs

from-list-homo : ∀ {X} {R : WRel X} (xs ys : List X) →
  let open PB R renaming (_≈_ to _≈₁_) in
  from-list (xs ++ ys) ≈₁ from-list xs • from-list ys
from-list-homo {R = R} [] ys = _≈₁_.sym _≈₁_.left-unit
  where open PB R renaming (_≈_ to _≈₁_)
from-list-homo {R = R} (x ∷ xs) ys =
    _≈₁_.trans
      (_≈₁_.cong _≈₁_.refl (from-list-homo xs ys))
      (_≈₁_.sym _≈₁_.assoc)
  where open PB R renaming (_≈_ to _≈₁_)

lemma-from-to : ∀ {w} → from-list (to-list w) ≈ w
lemma-from-to {[ x ]ʷ}  = right-unit
lemma-from-to {ε}        = refl
lemma-from-to {w • w₁}  with lemma-from-to {w} | lemma-from-to {w₁}
... | ih1 | ih2 = trans (from-list-homo (to-list w) (to-list w₁)) (cong ih1 ih2)

------------------------------------------------------------------------
-- The solver

-- Normalise a word up to associativity and units.
mod-assoc : ∀ w → Word X
mod-assoc w = from-list (to-list w)

-- Prove w ≈ v by comparing flattened generator lists (typically by
-- refl).
by-assoc : ∀ {w} {v} → to-list w ≡ to-list v → w ≈ v
by-assoc {w} {v} eq =
  trans (sym lemma-from-to) (trans (refl' (Eq.cong from-list eq)) lemma-from-to)

-- Chain a known equation a ≈ b with associativity steps on both sides.
by-assoc-and : ∀ {w} {v} {a} {b} →
  a ≈ b → to-list w ≡ to-list a → to-list b ≡ to-list v → w ≈ v
by-assoc-and {w} {v} {a} {b} eq eq1 eq2 =
  trans (by-assoc eq1) (trans eq (by-assoc eq2))

------------------------------------------------------------------------
-- Pattern-guided associativity solver

module Pattern-Assoc where

  -- Placeholder symbol for use in pattern words, e.g. (□ • □) • □.
  □ : Word ⊤
  □ = [ tt ]ʷ

  -- Like to-list, but guided by a pattern word: subwords at positions
  -- marked by □ are kept intact without further flattening.
  to-list-special : ∀ {X} → Word X → Word ⊤ → List (Word X)
  to-list-special w         ([ gen ]ʷ) = w ∷ []
  to-list-special ([ x ]ʷ) ε          = [ x ]ʷ ∷ []
  to-list-special ([ x ]ʷ) (p • q)    = [ x ]ʷ ∷ []
  to-list-special ε         ε          = []
  to-list-special ε         (p • q)    = []
  to-list-special (w • v)   ε          = to-list-special w ε ++ to-list-special v ε
  to-list-special (w • v)   (p • q)    = to-list-special w p ++ to-list-special v q

  flatten-word : ∀ {X} → Word (Word X) → Word X
  flatten-word ([ w ]ʷ) = w
  flatten-word ε         = ε
  flatten-word (w • v)   = flatten-word w • flatten-word v

  -- The empty relation: words of words up to associativity only.
  data ∅ {X : Set} : WRel X where

  lemma-flatten-word : ∀ {xs ys : Word (Word X)} →
    let open PB (∅ {Word X}) renaming (_≈_ to _≈₀_) in
    xs ≈₀ ys → flatten-word xs ≈ flatten-word ys
  lemma-flatten-word (axiom ())
  lemma-flatten-word refl           = refl
  lemma-flatten-word (sym hyp)      = sym (lemma-flatten-word hyp)
  lemma-flatten-word (trans hyp h₁) = trans (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word (cong hyp h₁)  = cong (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word assoc           = assoc
  lemma-flatten-word left-unit       = left-unit
  lemma-flatten-word right-unit      = right-unit

  lemma-to-list-special : ∀ (w : Word X) (p : Word ⊤) →
    flatten-word (from-list (to-list-special w p)) ≈ w
  lemma-to-list-special w         ([ gen ]ʷ) = right-unit
  lemma-to-list-special ([ x ]ʷ) ε          = right-unit
  lemma-to-list-special ([ x ]ʷ) (p • q)    = right-unit
  lemma-to-list-special ε         ε          = refl
  lemma-to-list-special ε         (p • q)    = refl
  lemma-to-list-special (w • v)   ε = begin
      flatten-word (from-list (to-list-special w ε ++ to-list-special v ε)) ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w ε) (to-list-special v ε)) ⟩
      flatten-word (from-list (to-list-special w ε) • from-list (to-list-special v ε)) ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w ε)) • flatten-word (from-list (to-list-special v ε)) ≈⟨ cong (lemma-to-list-special w ε) (lemma-to-list-special v ε) ⟩
      w • v ∎
    where open SR word-setoid
  lemma-to-list-special (w • v) (p • q) = begin
      flatten-word (from-list (to-list-special w p ++ to-list-special v q)) ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w p) (to-list-special v q)) ⟩
      flatten-word (from-list (to-list-special w p) • from-list (to-list-special v q)) ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w p)) • flatten-word (from-list (to-list-special v q)) ≈⟨ cong (lemma-to-list-special w p) (lemma-to-list-special v q) ⟩
      w • v ∎
    where open SR word-setoid

  -- Prove w ≈ v by giving matching pattern words p and q such that
  -- to-list-special w p ≡ to-list-special v q (checked by refl).
  --
  -- Example: to prove (a • b) • (c • d) ≈ a • (b • c) • d, write
  --   special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) refl
  special-assoc : ∀ {w v : Word X} (p q : Word ⊤) →
    to-list-special w p ≡ to-list-special v q → w ≈ v
  special-assoc {w = w} {v = v} p q hyp = begin
      w ≈⟨ sym (lemma-to-list-special w p) ⟩
      flatten-word (from-list (to-list-special w p)) ≈⟨ refl' (Eq.cong (λ □ → flatten-word (from-list □)) hyp) ⟩
      flatten-word (from-list (to-list-special v q)) ≈⟨ lemma-to-list-special v q ⟩
      v ∎
    where open SR word-setoid
