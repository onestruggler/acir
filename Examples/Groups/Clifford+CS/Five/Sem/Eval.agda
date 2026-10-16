------------------------------------------------------------------------
-- Presentations of groups
--
-- A circuit's semantics against a given operator, by evaluation
--
-- SemanticSteps.Same compares two circuits by one boolean on their
-- row-operation readings; `SameOp u l M` compares a circuit with the
-- scaled operator (l , M), tabulated as a trie, the same way, and
-- `same-op` turns the boolean into `⟦ u ⟧ ~ (l , M)`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Eval where

open import Data.Bool using (true)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Word.Base using (_•_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len ; ⟦_⟧ₒ ; ⟦⟧ₒ-•)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.Evaluation using (⟦_⟧R ; ⟦⟧R≡⟦⟧M)

private
  variable
    k : ℕ

SameOp : (u : Circuit k) (l : ℕ) (M : Op k) → Set
SameOp u l M = eqM (scaleM (γ^ l) ⟦ u ⟧R) (scaleM (γ^ len u) (matOf M)) ≡ true

same-op : (u : Circuit k) (l : ℕ) (M : Op k) → SameOp u l M → ⟦ u ⟧ ~ (l , M)
same-op u l M e =
  ≐-trans (·-cong Eq.refl (⟦⟧-ix u))
    (≐-trans (≐-sym (ix-scaleM (γ^ l) ⟦ u ⟧M))
      (≐-trans (ix-≡ (Eq.subst (λ A → scaleM (γ^ l) A ≡ scaleM (γ^ len u) (matOf M)) (⟦⟧R≡⟦⟧M u)
                        (eqM-sound _ _ e)))
        (≐-trans (ix-scaleM (γ^ len u) (matOf M)) (·-cong Eq.refl (ix-matOf M)))))

-- The product, read through the semantics.
hom : (a b : Circuit k) → ⟦ a • b ⟧ ~ (⟦ a ⟧ ∙ ⟦ b ⟧)
hom a b = ~-reflexive {l = len a +ℕ len b} {len a +ℕ len b} {M = ⟦ a • b ⟧ₒ} {⟦ a ⟧ₒ ⊙ ⟦ b ⟧ₒ}
            Eq.refl (⟦⟧ₒ-• a b)
