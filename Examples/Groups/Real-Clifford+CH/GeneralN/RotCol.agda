------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations of the decoding, and their placed commutation
-- (Clément, Appendix E.5)
--
-- `rot β` is the multi-controlled ZX (β true) or XZ (β false) on wire 0,
-- controlled by every other wire — the base gate of the decoded
-- (−1)_[a] X_[a,a+1] (`mc±XZ β L = conj₁ L (rot β)`, `mc±XZ-rot`).
-- `RotComm m` says that two such rotations, placed and coloured, commute
-- when their colourings differ on a wire off both targets: the paper's
-- (351) and (352) with x ≠ y, in every position.  Like Col, this module
-- has no parameters, so that the proof at width 5 + k (RotAnywhere) and
-- the rules that use it (Lemma88.Rule32) spell the statement alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.RotCol where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Layout ; conj₁ ; mc±XZ ; Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (_⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

rot : ∀ {m} → Bool → Circuit (₃₊ m)
rot {m} true  = ΛZX (₂₊ m)
rot {m} false = ΛXZ (₂₊ m)

mc±XZ-rot : ∀ {m} β (L : Layout (₃₊ m)) → mc±XZ β L ≡ conj₁ L (rot β)
mc±XZ-rot true  L = Eq.refl
mc±XZ-rot false L = Eq.refl

-- The family of rotations with no control on wire 0 left out: ZX for
-- true, XZ for false (rot β is F β (2 + m)).
F : Bool → (K : ℕ) → Circuit (₁₊ K)
F true  = ΛZX
F false = ΛXZ

-- (354) on the top wire of 1 + K wires.
TopMerge : Bool → ℕ → Set
TopMerge β K = (₂₊ K) ⊢ (Xat (suc K) • F β (suc K) • Xat (suc K)) • F β (suc K) ≈ placeAt (suc K) (F β K)

RotComm : ℕ → Set
RotComm m =
  ∀ α β (u u′ : Word (S.Gen (₃₊ m))) (t t′ : Fin (₃₊ m)) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
  (s s′ : Bits (₃₊ m)) → lookupℕ (toℕ t) s ≡ true → lookupℕ (toℕ t′) s′ ≡ true →
  (j : Fin (₃₊ m)) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≢ lookupℕ (toℕ j) s′ →
  (₃₊ m) ⊢ place u s (rot α) • place u′ s′ (rot β) ≈ place u′ s′ (rot β) • place u s (rot α)

-- The canonical cases, in the frame of the placement: two colourings of
-- the rotation on wire 0, relatively white on wire 1 (351) …
C351 : ℕ → Set
C351 m = ∀ α β (x y : Bits (₃₊ m)) → lookupℕ 0 x ≡ true → lookupℕ 0 y ≡ true →
         (lookupℕ 1 x ⇔ lookupℕ 1 y) ≡ false →
         (₃₊ m) ⊢ col x (rot α) • col y (rot β) ≈ col y (rot β) • col x (rot α)

-- … and the rotations on the wires 0 and 1, relatively white on wire 2
-- (352).
C352 : ℕ → Set
C352 m = ∀ α β (x y : Bits (₃₊ m)) → lookupℕ 0 x ≡ true → lookupℕ 1 y ≡ true →
         (lookupℕ 2 x ⇔ lookupℕ 2 y) ≡ false →
         (₃₊ m) ⊢ col x (rot α) • col y (Ex • rot β • Ex) ≈ col y (Ex • rot β • Ex) • col x (rot α)

-- The pair step: a rotation on wire 0 against the box on wire 1, in the
-- four colourings of the wires 0 1, is turned over by it …
PairCanon : ℕ → Set
PairCanon m = ∀ β γ δ →
  (₃₊ m) ⊢ rot β • col (γ ∷ δ ∷ replicate (₁₊ m) true) (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) ≈
           col (γ ∷ δ ∷ replicate (₁₊ m) true) (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) • rot (not β)

-- … and placed, with colourings agreeing off the two targets.
PairStep : ℕ → Set
PairStep m = ∀ β (u u′ : Word (S.Gen (₃₊ m))) (t t′ : Fin (₃₊ m)) → t′ ≢ t →
  perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F → (s s′ : Bits (₃₊ m)) →
  (∀ (j : Fin (₃₊ m)) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≡ lookupℕ (toℕ j) s′) →
  (₃₊ m) ⊢ place u s (rot β) • place u′ s′ (Λ□ (₂₊ m)) ≈ place u′ s′ (Λ□ (₂₊ m)) • place u s (rot (not β))
