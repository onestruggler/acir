------------------------------------------------------------------------
-- Presentations of groups
--
-- A proved equation between lists may be used in any list context.
-- This small lemma checks the local rewrite certificates used when
-- shortening the finite Clément relators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (WRel)

module Examples.Groups.CCX+HH.RelatorRewriting {X : Set} (Γ : WRel X) where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Presentation.Base Γ
open import Presentation.Tactic.AssociativitySolver
open Assoc Γ renaming (from-list to read)

context : ∀ (prefix suffix : List X) {u v} → read u ≈ read v →
  read (prefix ++ (u ++ suffix)) ≈ read (prefix ++ (v ++ suffix))
context [] suffix {u} {v} p =
  trans (fl-homo u suffix) (trans (cong p refl) (sym (fl-homo v suffix)))
context (x ∷ prefix) suffix p = cong refl (context prefix suffix p)
