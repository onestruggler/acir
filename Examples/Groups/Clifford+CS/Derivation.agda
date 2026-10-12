------------------------------------------------------------------------
-- Presentations of groups
--
-- The format of machine-found derivations
--
-- Derivations between circuits are found off-line, by a Knuth–Bendix
-- completion that records how each rule it adds follows from the ones
-- before (scratchpad kb.py), and written out as chains of rewrites of
-- letter lists: a step rewrites the factor l of the list p ++ l ++ s to
-- r, by a rule l ≈ r proved before (`ctx`).  Lists are read as words by
-- `from-list`, and ⌊_⌋ / ⌈_⌉ move between an equation of words and the
-- equation of their letter lists.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

module Examples.Groups.Clifford+CS.Derivation {X : Set} (Γ : WRel X) where

open import Data.List using (List ; [] ; _∷_ ; _++_)

import Presentation.Base as PB
open PB Γ
open import Presentation.Tactic.AssociativitySolver using (module Assoc)
open Assoc Γ public using (to-list ; from-list)
open Assoc Γ using (fl-homo ; lemma-ft)

-- A rewrite in context.
ctx : ∀ (p l r s : List X) → from-list l ≈ from-list r →
      from-list (p ++ l ++ s) ≈ from-list (p ++ r ++ s)
ctx p l r s e =
  trans (fl-homo p (l ++ s))
    (trans (cong refl (trans (fl-homo l s) (trans (cong e refl) (sym (fl-homo r s)))))
           (sym (fl-homo p (r ++ s))))

-- An equation of words, as one of their letter lists, and back.
⌊_⌋ : ∀ {w v} → w ≈ v → from-list (to-list w) ≈ from-list (to-list v)
⌊ e ⌋ = trans lemma-ft (trans e (sym lemma-ft))

⌈_⌉ : ∀ {w v} → from-list (to-list w) ≈ from-list (to-list v) → w ≈ v
⌈ e ⌉ = trans (sym lemma-ft) (trans e lemma-ft)

-- Steps are chained by transitivity.
infixr 4 _⨾_
_⨾_ : ∀ {u v w} → u ≈ v → v ≈ w → u ≈ w
_⨾_ = trans
