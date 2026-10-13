------------------------------------------------------------------------
-- Presentations of groups
--
-- Short signed-permutation normalization from Table 1.  Every signed
-- factor occurring in the four-state Schreier decoder has at most two
-- sign letters and two exchanges.  The lemmas below move its signs
-- left, yielding one sign pair and one double exchange, without a
-- general permutation-synthesis theorem or an assumption on overlaps.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+H.GeneralN.SignedNormalization {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
open import Presentation.Base (U._===_ {n}) hiding (_===_)
open import Presentation.Properties (U._===_ {n}) using (word-setoid)
open import Relation.Binary.Reasoning.Setoid word-setoid

swap : Fin n → Fin n → Fin n → Fin n
swap a b c with c ≟ a
... | yes _ = b
... | no _ with c ≟ b
...   | yes _ = a
...   | no _ = c

exchange-sign : ∀ a b .(p : a < b) c →
  U.X a b p • U.M c ≈ U.M (swap a b c) • U.X a b p
exchange-sign a b p c with c ≟ a
... | yes Eq.refl = sym (D.flip (U.X-gen a b p) (sym (axiom (U.r3c p))))
... | no ca with c ≟ b
...   | yes Eq.refl = axiom (U.r3c p)
...   | no cb = axiom (U.r2b p ca cb)

module Pair (a b c d : Fin n) .(ab : a < b) .(cd : c < d) where
  private
    X Y : Word (U.Gen n)
    X = U.X a b ab
    Y = U.X c d cd
    σ τ : Fin n → Fin n
    σ = swap a b
    τ = swap c d

  -- One exchange can move across two consecutive signs.
  XMM : ∀ i j → X • (U.M i • U.M j) ≈
    (U.M (σ i) • U.M (σ j)) • X
  XMM i j = begin
    X • (U.M i • U.M j) ≈⟨ sym assoc ⟩
    (X • U.M i) • U.M j ≈⟨ cong (exchange-sign a b ab i) refl ⟩
    (U.M (σ i) • X) • U.M j ≈⟨ assoc ⟩
    U.M (σ i) • (X • U.M j) ≈⟨ cong refl (exchange-sign a b ab j) ⟩
    U.M (σ i) • (U.M (σ j) • X) ≈⟨ sym assoc ⟩
    (U.M (σ i) • U.M (σ j)) • X ∎

  -- Two exchanges move across one sign by composing their index swaps.
  XXM : ∀ i → (X • Y) • U.M i ≈ U.M (σ (τ i)) • (X • Y)
  XXM i = begin
    (X • Y) • U.M i ≈⟨ assoc ⟩
    X • (Y • U.M i) ≈⟨ cong refl (exchange-sign c d cd i) ⟩
    X • (U.M (τ i) • Y) ≈⟨ sym assoc ⟩
    (X • U.M (τ i)) • Y ≈⟨ cong (exchange-sign a b ab (τ i)) refl ⟩
    (U.M (σ (τ i)) • X) • Y ≈⟨ assoc ⟩
    U.M (σ (τ i)) • (X • Y) ∎

  MXMX : ∀ i j → (U.M i • X) • (U.M j • Y) ≈
    (U.M i • U.M (σ j)) • (X • Y)
  MXMX i j = begin
    (U.M i • X) • (U.M j • Y) ≈⟨ assoc ⟩
    U.M i • (X • (U.M j • Y)) ≈⟨ cong refl (sym assoc) ⟩
    U.M i • ((X • U.M j) • Y) ≈⟨ cong refl (cong (exchange-sign a b ab j) refl) ⟩
    U.M i • ((U.M (σ j) • X) • Y) ≈⟨ cong refl assoc ⟩
    U.M i • (U.M (σ j) • (X • Y)) ≈⟨ sym assoc ⟩
    (U.M i • U.M (σ j)) • (X • Y) ∎

  MXXM : ∀ i j → (U.M i • (X • Y)) • U.M j ≈
    (U.M i • U.M (σ (τ j))) • (X • Y)
  MXXM i j = begin
    (U.M i • (X • Y)) • U.M j ≈⟨ assoc ⟩
    U.M i • ((X • Y) • U.M j) ≈⟨ cong refl (XXM j) ⟩
    U.M i • (U.M (σ (τ j)) • (X • Y)) ≈⟨ sym assoc ⟩
    (U.M i • U.M (σ (τ j))) • (X • Y) ∎

  XMXM : ∀ i j → (X • U.M i) • (Y • U.M j) ≈
    (U.M (σ i) • U.M (σ (τ j))) • (X • Y)
  XMXM i j = begin
    (X • U.M i) • (Y • U.M j)
      ≈⟨ cong (exchange-sign a b ab i) refl ⟩
    (U.M (σ i) • X) • (Y • U.M j)
      ≈⟨ trans assoc (trans (cong refl (sym assoc)) (sym assoc)) ⟩
    (U.M (σ i) • (X • Y)) • U.M j ≈⟨ MXXM (σ i) j ⟩
    (U.M (σ i) • U.M (σ (τ j))) • (X • Y) ∎

  XXMM : ∀ i j → (X • Y) • (U.M i • U.M j) ≈
    (U.M (σ (τ i)) • U.M (σ (τ j))) • (X • Y)
  XXMM i j = begin
    (X • Y) • (U.M i • U.M j) ≈⟨ sym assoc ⟩
    ((X • Y) • U.M i) • U.M j ≈⟨ cong (XXM i) refl ⟩
    (U.M (σ (τ i)) • (X • Y)) • U.M j ≈⟨ MXXM (σ (τ i)) j ⟩
    (U.M (σ (τ i)) • U.M (σ (τ j))) • (X • Y) ∎
