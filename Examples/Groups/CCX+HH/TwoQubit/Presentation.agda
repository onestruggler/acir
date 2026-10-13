------------------------------------------------------------------------
-- Clément-style completeness for two-wire X,CX,HH circuits.
--
-- The auxiliary theory is Table 1 at dimension four.  Its three-coset
-- Schreier decoder gives 3 × 58 translated equations plus four circuit
-- generator roundtrips.  The finite state and factorization obligations
-- are proved in Table and Soundness.  Semantics identifies the encoding
-- with the independently specified ordinary four-by-four gate matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Presentation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
open import Examples.Groups.CCX+HH.TwoQubit.Table public
  using (_===_ ; _≈_ ; roundtrip ; translated)
open import Examples.Groups.CCX+HH.TwoQubit.Table using (encoded-completeness)
open import Examples.Groups.CCX+HH.TwoQubit.Soundness using (encoded-soundness)
open import Examples.Groups.CCX+HH.TwoQubit.Semantics public using (⟦_⟧ ; encoding-correct)

soundness : ∀ {u v : Circuit 2} → u ≈ v → ⟦ u ⟧ ≡ ⟦ v ⟧
soundness {u} {v} proof =
  Eq.trans (Eq.sym (encoding-correct u))
    (Eq.trans (encoded-soundness proof) (encoding-correct v))

completeness : ∀ {u v : Circuit 2} → ⟦ u ⟧ ≡ ⟦ v ⟧ → u ≈ v
completeness {u} {v} equality = encoded-completeness
  (Eq.trans (encoding-correct u)
    (Eq.trans equality (Eq.sym (encoding-correct v))))
