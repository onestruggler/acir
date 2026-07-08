------------------------------------------------------------------------
-- Presentations of groups
--
-- An associativity solver for the congruence ≈ of a presentation.
--
-- to-list flattens a word to its list of generators (dropping the
-- bracketing and units); by-assoc then proves w ≈ v by comparing the
-- flattened lists (typically by refl).  Pattern-Assoc is the
-- pattern-guided variant: by-passoc re-brackets guided by pattern
-- words built from □.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.MonoidCongruence.Solver where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

import Word.Relation.Binary.MonoidCongruence as PB
open import Word.Base

module Assoc {X : Set} (Γ : WRel X) where

  open PB Γ

  ------------------------------------------------------------------------
  -- Flatten a word to its list of generators, and back

  to-list : Word X → List X
  to-list [ x ]ʷ   = x ∷ []
  to-list ε        = []
  to-list (w • w₁) = to-list w ++ to-list w₁

  from-list : List X → Word X
  from-list []       = ε
  from-list (x ∷ xs) = [ x ]ʷ • from-list xs

  fl-homo : (xs ys : List X) →
    from-list (xs ++ ys) ≈ from-list xs • from-list ys
  fl-homo [] ys = sym left-unit
  fl-homo (x ∷ xs) ys =
      trans (cong refl (fl-homo xs ys)) (sym assoc)

  lemma-ft : ∀ {w} → from-list (to-list w) ≈ w
  lemma-ft {[ x ]ʷ} = right-unit
  lemma-ft {ε}      = refl
  lemma-ft {w • w₁} with lemma-ft {w} | lemma-ft {w₁}
  ... | ih1 | ih2 = trans (fl-homo (to-list w) (to-list w₁)) (cong ih1 ih2)

  ------------------------------------------------------------------------
  -- The solver

  -- Normalise a word up to associativity and units.
  mod-assoc : ∀ w → Word X
  mod-assoc w = from-list (to-list w)

  -- Prove w ≈ v by comparing flattened generator lists (typically by
  -- refl).
  by-assoc : ∀ {w} {v} → to-list w ≡ to-list v → w ≈ v
  by-assoc {w} {v} eq =
    trans (sym lemma-ft) (trans (refl' (Eq.cong from-list eq)) lemma-ft)

  -- Chain a known equation a ≈ b with associativity steps on both sides.
  by-assoc-and : ∀ {w} {v} {a} {b} →
    a ≈ b → to-list w ≡ to-list a → to-list b ≡ to-list v → w ≈ v
  by-assoc-and {w} {v} {a} {b} eq eq1 eq2 =
    trans (by-assoc eq1) (trans eq (by-assoc eq2))

------------------------------------------------------------------------
-- Pattern-guided associativity solver

module Pattern-Assoc {X : Set} (Γ : WRel X) where

  open PB Γ
  open import Word.Relation.Binary.MonoidCongruence.Setoid Γ using (word-setoid)

  -- Placeholder symbol for use in pattern words, e.g. (□ • □) • □.
  □ : Word ⊤
  □ = [ tt ]ʷ

  -- Like to-list, but guided by a pattern word: subwords at positions
  -- marked by □ are kept intact without further flattening.
  to-list-pat : ∀ {X} → Word X → Word ⊤ → List (Word X)
  to-list-pat w         ([ gen ]ʷ) = w ∷ []
  to-list-pat ([ x ]ʷ)  ε          = [ x ]ʷ ∷ []
  to-list-pat ([ x ]ʷ)  (p • q)    = [ x ]ʷ ∷ []
  to-list-pat ε         ε          = []
  to-list-pat ε         (p • q)    = []
  to-list-pat (w • v)   ε          = to-list-pat w ε ++ to-list-pat v ε
  to-list-pat (w • v)   (p • q)    = to-list-pat w p ++ to-list-pat v q

  -- The empty relation: words of words up to associativity only.
  data ∅ {X : Set} : WRel X where

  open Assoc (∅ {Word X})

  private
    wconcat-cong : ∀ {xs ys : Word (Word X)} →
      let open PB (∅ {Word X}) renaming (_≈_ to _≈₀_) in
      xs ≈₀ ys → wconcat xs ≈ wconcat ys
    wconcat-cong (axiom ())
    wconcat-cong refl         = refl
    wconcat-cong (sym hyp)    = sym (wconcat-cong hyp)
    wconcat-cong (trans h h') = trans (wconcat-cong h) (wconcat-cong h')
    wconcat-cong (cong h h')  = cong (wconcat-cong h) (wconcat-cong h')
    wconcat-cong assoc        = assoc
    wconcat-cong left-unit    = left-unit
    wconcat-cong right-unit   = right-unit

  -- shorthands for shortening the proof.
  private
    wt = wconcat
    fl = from-list
    tlp = to-list-pat
    wt-cong = wconcat-cong
    flh = fl-homo
  

  lemma-tlp : ∀ (w : Word X) (p : Word ⊤) →
    wt (fl (tlp w p)) ≈ w
  lemma-tlp w         ([ gen ]ʷ) = right-unit
  lemma-tlp ([ x ]ʷ) ε           = right-unit
  lemma-tlp ([ x ]ʷ) (p • q)     = right-unit
  lemma-tlp ε         ε          = refl
  lemma-tlp ε         (p • q)    = refl
  lemma-tlp (w • v)   ε = begin
    wt (fl (tlp w ε ++ tlp v ε))          ≈⟨ wt-cong (flh (tlp w ε) (tlp v ε)) ⟩
    wt (fl (tlp w ε) • fl (tlp v ε))      ≈⟨ refl ⟩
    wt (fl (tlp w ε)) • wt (fl (tlp v ε)) ≈⟨ cong (lemma-tlp w ε) (lemma-tlp v ε) ⟩
    w • v ∎
    where open SR word-setoid
    
  lemma-tlp (w • v) (p • q) = begin
    wt (fl (tlp w p ++ tlp v q))          ≈⟨ wt-cong (flh (tlp w p) (tlp v q)) ⟩
    wt (fl (tlp w p) • fl (tlp v q))      ≈⟨ refl ⟩
    wt (fl (tlp w p)) • wt (fl (tlp v q)) ≈⟨ cong (lemma-tlp w p) (lemma-tlp v q) ⟩
    w • v ∎
    where open SR word-setoid

  -- Prove w ≈ v by giving matching pattern words p and q such that
  -- tlp w p ≡ tlp v q (checked by refl).
  --
  -- Example: to prove (a • b) • (c • d) ≈ a • (b • c) • d, write
  --   by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) refl
  by-passoc : ∀ {w v : Word X} (p q : Word ⊤) →
    tlp w p ≡ tlp v q → w ≈ v
  by-passoc {w = w} {v = v} p q hyp = begin
    w ≈⟨ sym (lemma-tlp w p) ⟩
    wt (fl (tlp w p)) ≈⟨ refl' (Eq.cong (λ □ → wt (fl □)) hyp) ⟩
    wt (fl (tlp v q)) ≈⟨ lemma-tlp v q ⟩
    v ∎
    where open SR word-setoid
