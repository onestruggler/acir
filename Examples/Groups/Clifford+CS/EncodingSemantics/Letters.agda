------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level letters read on bit vectors, at the Gray numbering
--
-- A letter's scaled operator (BridgeGray.⟦_⟧ʸ) is a table over the
-- indices; read at the basis vectors, the phase i_[idx s] is the
-- diagonal with i at s, and δ at two indices is δ at their vectors.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Letters (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

import Data.Fin.Properties as FinP

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Encoding m using (n ; idx ; idx-inj)
open import Examples.Groups.Clifford+CS.BridgeGray n
  using (⟦_⟧Y ; coefℤ ; δᶠ ; δᶠ-refl ; δᶠ-≢ ; ci-a ; ci-≢)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag using (diag ; δb-≢)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (eqB-complete ; eqB-false)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

------------------------------------------------------------------------
-- δ at two indices is δ at their vectors

δᶠ-idx : ∀ (x y : Bits n) → δᶠ (idx x) (idx y) ≡ δb x y
δᶠ-idx x y = go (idx x FinP.≟ idx y)
  where
  go : Dec (idx x ≡ idx y) → δᶠ (idx x) (idx y) ≡ δb x y
  go (yes e) = Eq.subst (λ y → δᶠ (idx x) (idx y) ≡ δb x y) (idx-inj e)
                 (Eq.trans (δᶠ-refl (idx x)) (Eq.sym (δb-refl x)))
  go (no ne) = Eq.trans (δᶠ-≢ ne) (Eq.sym (δb-≢ x y (λ e → ne (Eq.cong idx e))))

------------------------------------------------------------------------
-- The phase letters

-- The phase i at the basis vector s.
phs : Bits n → Bits n → 𝔽
phs s x = if eqB x s then ⅈ else 1#

phs-hit : ∀ s x → x ≡ s → phs s x ≡ ⅈ
phs-hit s x e = Eq.cong (λ b → if b then ⅈ else 1#) (eqB-complete x s e)

phs-miss : ∀ s x → x ≢ s → phs s x ≡ 1#
phs-miss s x ne = Eq.cong (λ b → if b then ⅈ else 1#) (eqB-false x s ne)

-- The letter i_[s], read on bit vectors.
i-M : ∀ (s : Bits n) → proj₂ ⟦ TL.i (idx s) ⟧Y ≐ diag (phs s)
i-M s x y = go (idx x FinP.≟ idx s)
  where
  go : Dec (idx x ≡ idx s) → coefℤ (TL.i-gen (idx s)) (idx x) (idx y) ≡ phs s x * δb x y
  go (yes e) = begin
    coefℤ (TL.i-gen (idx s)) (idx x) (idx y)
      ≡⟨ Eq.cong (λ a → coefℤ (TL.i-gen a) (idx x) (idx y)) (Eq.sym e) ⟩
    coefℤ (TL.i-gen (idx x)) (idx x) (idx y)
      ≡⟨ ci-a (idx x) (idx y) ⟩
    δᶠ (idx x) (idx y) * ⅈ
      ≡⟨ Eq.cong (_* ⅈ) (δᶠ-idx x y) ⟩
    δb x y * ⅈ
      ≡⟨ *-comm (δb x y) ⅈ ⟩
    ⅈ * δb x y
      ≡⟨ Eq.cong (_* δb x y) (Eq.sym (phs-hit s x (idx-inj e))) ⟩
    phs s x * δb x y ∎
    where open Eq.≡-Reasoning
  go (no ne) = begin
    coefℤ (TL.i-gen (idx s)) (idx x) (idx y)
      ≡⟨ ci-≢ (idx s) ne (idx y) ⟩
    δᶠ (idx x) (idx y)
      ≡⟨ δᶠ-idx x y ⟩
    δb x y
      ≡⟨ Eq.sym (*-identityˡ (δb x y)) ⟩
    1# * δb x y
      ≡⟨ Eq.cong (_* δb x y) (Eq.sym (phs-miss s x (λ e → ne (Eq.cong idx e)))) ⟩
    phs s x * δb x y ∎
    where open Eq.≡-Reasoning
