------------------------------------------------------------------------
-- Presentations of groups
--
-- The index-four auxiliary subgroup of O_N(Z[1/2]).
--
-- Its elements are exactly the source words with charge 00 under the
-- action in Action.agda.  The formal Schreier alphabet is finite at
-- each fixed dimension, and its complete relations are obtained from
-- Table 1 by the stateful Clément translation.
--
-- This is an auxiliary presentation.  Identifying its generators with
-- physical CCX+HH circuits is a separate constructive decoding step.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin ; _<_)

module Examples.Groups.CCX+HH.Subgroup.PresentationAt
  (N : ℕ) (a b : Fin N) .(a<b : a < b) where

open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH.Subgroup.Action
import Examples.Groups.CCX+HH.Subgroup.Schreier as Schreier

open At N public using (state ; state-relations ; state-cong)

rep : Coset → Word (T.Gen N)
rep c00 = ε
rep c10 = T.M a
rep c11 = T.X a b a<b
rep c01 = T.M a • T.X a b a<b

rep-state : ∀ c → state c00 (rep c) ≡ c
rep-state c00 = Eq.refl
rep-state c10 = Eq.refl
rep-state c11 = Eq.refl
rep-state c01 = Eq.refl

module Theory = Schreier (T._===_ {N}) D.grouplike c00
  dyadic-step state-relations rep PB.refl rep-state

open Theory public using
  (Edge ; e ; encode ; decode ; _===_ ; _≈_ ; roundtrip ; translated
  ; encode-injective ; encode-cong ; encode-closed ; edge-closed
  ; factor-word ; decode-loop ; grouplike)

-- Exact completeness and soundness for the inherited dyadic matrices.
completeness : ∀ {u v : Word Edge} →
  S.⟦ encode u ⟧ᵐ ≡ S.⟦ encode v ⟧ᵐ → u ≈ v
completeness eq = encode-injective (Main.completeness eq)

soundness : ∀ {u v : Word Edge} → u ≈ v →
  S.⟦ encode u ⟧ᵐ ≡ S.⟦ encode v ⟧ᵐ
soundness eq = Red.sound-act (encode-cong eq) S.𝕀

-- The charge is a property of the matrix, not merely of its word.
state-semantic : ∀ c {u v : Word (T.Gen N)} →
  S.⟦ u ⟧ᵐ ≡ S.⟦ v ⟧ᵐ → state c u ≡ state c v
state-semantic c {u} {v} eq = state-cong c (Main.completeness {u = u} {v = v} eq)

-- The image is exactly the charge-00 subgroup: encode-closed is one
-- inclusion, and this explicit reconstruction is the other.
stabilizer-generated : ∀ w → state c00 w ≡ c00 →
  S.⟦ encode (decode c00 w) ⟧ᵐ ≡ S.⟦ w ⟧ᵐ
stabilizer-generated w closed = Red.sound-act (decode-loop {w} closed) S.𝕀
