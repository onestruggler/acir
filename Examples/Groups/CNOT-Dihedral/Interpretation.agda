------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of CNOT-dihedral circuits as operators:
-- ⟦_⟧ : Circuit n → Op n
--
-- A word denotes the composite of its letters' operators, read left to
-- right.  The reading is abstract — a circuit's operator is compared by
-- comparing circuits, never by unfolding a long product — with its
-- defining equations exported as lemmas (⟦⟧-gen, ⟦⟧-ε, ⟦⟧-•).  The
-- library's reading through the monoid (Ext.⟦_⟧ᴱ) equals it (⟦⟧ᴱ-def).
--
-- A circuit is also read as a table, ⟦_⟧M, where the relations are
-- decided by `refl`; `localise` connects the two, so that a relation
-- checked at the width it is drawn on holds at every width (by-relator).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Interpretation where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT-Dihedral.Semantics
open import Examples.Groups.CNOT-Dihedral.Syntactics

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : Gen n → Op n
⟦ ω-gen    ⟧ᵍ = ωₒ
⟦ X-gen    ⟧ᵍ = Xₒ
⟦ T-gen    ⟧ᵍ = Tₒ
⟦ CNOT-gen ⟧ᵍ = CNOTₒ
⟦ SWAP-gen ⟧ᵍ = SWAPₒ
⟦ g ↥      ⟧ᵍ = up ⟦ g ⟧ᵍ

abstract
  ⟦_⟧ : Circuit n → Op n
  ⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
  ⟦ ε ⟧      = Idₒ
  ⟦ w • v ⟧  = ⟦ w ⟧ ⊙ ⟦ v ⟧

  ⟦⟧-gen : (g : Gen n) → ⟦ [ g ]ʷ ⟧ ≐ ⟦ g ⟧ᵍ
  ⟦⟧-gen g = ≐-refl ⟦ g ⟧ᵍ

  ⟦⟧-ε : ⟦_⟧ {n} ε ≐ Idₒ
  ⟦⟧-ε = ≐-refl Idₒ

  ⟦⟧-• : (w v : Circuit n) → ⟦ w • v ⟧ ≐ (⟦ w ⟧ ⊙ ⟦ v ⟧)
  ⟦⟧-• w v = ≐-refl (⟦ w ⟧ ⊙ ⟦ v ⟧)

  ⟦⟧-•₃ : (a b c : Circuit n) → ⟦ a • (b • c) ⟧ ≐ (⟦ a ⟧ ⊙ (⟦ b ⟧ ⊙ ⟦ c ⟧))
  ⟦⟧-•₃ a b c = ≐-refl (⟦ a ⟧ ⊙ (⟦ b ⟧ ⊙ ⟦ c ⟧))

-- The same reading as StarInterp builds it from the monoid, for the
-- presentation machinery; the two agree on the nose.
module Ext (n : ℕ) where
  open import Normalization.StarInterp (n VRel,_===_)
  open Extend (Op-monoid n) ⟦_⟧ᵍ public
    renaming (⟦_⟧ to ⟦_⟧ᴱ)

abstract
  ⟦⟧ᴱ-def : (w : Circuit n) → Ext.⟦_⟧ᴱ n w ≡ ⟦ w ⟧
  ⟦⟧ᴱ-def [ g ]ʷ  = Eq.refl
  ⟦⟧ᴱ-def ε       = Eq.refl
  ⟦⟧ᴱ-def (w • v) = Eq.cong₂ _⊙_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)

⟦⟧ᴱ-≐ : {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → Ext.⟦_⟧ᴱ n w ≐ Ext.⟦_⟧ᴱ n v
⟦⟧ᴱ-≐ {w = w} {v} = Eq.subst₂ _≐_ (Eq.sym (⟦⟧ᴱ-def w)) (Eq.sym (⟦⟧ᴱ-def v))

≐-⟦⟧ᴱ : {w v : Circuit n} → Ext.⟦_⟧ᴱ n w ≐ Ext.⟦_⟧ᴱ n v → ⟦ w ⟧ ≐ ⟦ v ⟧
≐-⟦⟧ᴱ {w = w} {v} = Eq.subst₂ _≐_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)

------------------------------------------------------------------------
-- The stored reading

valMat : Gen k → Mat k
valMat g = matOf ⟦ g ⟧ᵍ

⟦_⟧M : Circuit k → Mat k
⟦ [ g ]ʷ ⟧M = valMat g
⟦ ε ⟧M      = matOf Idₒ
⟦ w • v ⟧M  = mulM ⟦ w ⟧M ⟦ v ⟧M

------------------------------------------------------------------------
-- Localisation
--
-- A circuit written at width k, read at width k + n, is its own
-- operator acting on the bottom k wires.

localise-gen : (g : Gen k) → ⟦ g ↧ᵏ n ⟧ᵍ ≐ emb {k} {n} ⟦ g ⟧ᵍ
localise-gen {k} {n} ω-gen = ≐-sym (emb-ω {k} {n})
localise-gen X-gen    = ≐-sym emb-X
localise-gen T-gen    = ≐-sym emb-T
localise-gen CNOT-gen = ≐-sym emb-CNOT
localise-gen SWAP-gen = ≐-sym emb-SWAP
localise-gen (g ↥)    = ≐-trans (up-cong (localise-gen g)) (≐-sym (emb-up ⟦ g ⟧ᵍ))

abstract
  localise : (w : Circuit k) → ⟦ w ↓ᵏ n ⟧ ≐ emb {k} {n} ⟦ w ⟧
  localise [ g ]ʷ    = localise-gen g
  localise {k} {n} ε = ≐-sym (emb-id {k} {n})
  localise (w • v)   =
    ≐-trans (⊙-cong (localise w) (localise v)) (≐-sym (emb-⊙ ⟦ w ⟧ ⟦ v ⟧))

  -- At its own width, a circuit's operator is its table.
  ⟦⟧-ix : (w : Circuit k) → ⟦ w ⟧ ≐ ix ⟦ w ⟧M
  ⟦⟧-ix [ g ]ʷ  = ≐-sym (ix-matOf ⟦ g ⟧ᵍ)
  ⟦⟧-ix ε       = ≐-sym (ix-matOf Idₒ)
  ⟦⟧-ix (w • v) =
    ≐-trans (⊙-cong (⟦⟧-ix w) (⟦⟧-ix v)) (≐-sym (ix-mul ⟦ w ⟧M ⟦ v ⟧M))

  -- Shifting a circuit shifts its operator.
  up-word : (w : Circuit n) → ⟦ w ↑ ⟧ ≐ up ⟦ w ⟧
  up-word [ g ]ʷ  = ≐-refl (up ⟦ g ⟧ᵍ)
  up-word ε       = ≐-sym up-Id
  up-word (w • v) =
    ≐-trans (⊙-cong (up-word w) (up-word v)) (≐-sym (up-⊙ ⟦ w ⟧ ⟦ v ⟧))

------------------------------------------------------------------------
-- One table identity, at every width

by-matrix : (u v : Circuit k) → ⟦ u ⟧M ≡ ⟦ v ⟧M → ⟦ u ↓ᵏ n ⟧ ≐ ⟦ v ↓ᵏ n ⟧
by-matrix u v eq =
  ≐-trans (localise u)
    (≐-trans (emb-cong (≐-trans (⟦⟧-ix u) (≐-trans (ix-≡ eq) (≐-sym (⟦⟧-ix v)))))
             (≐-sym (localise v)))

-- For an axiom spelled at its own width: the two words are the padded
-- relators, an equation of words decided on data.
by-relator : (u v : Circuit k) {u′ v′ : Circuit (k +ℕ n)} →
             u ↓ᵏ n ≡ u′ → v ↓ᵏ n ≡ v′ → ⟦ u ⟧M ≡ ⟦ v ⟧M → ⟦ u′ ⟧ ≐ ⟦ v′ ⟧
by-relator u v Eq.refl Eq.refl eq = by-matrix u v eq
