------------------------------------------------------------------------
-- Presentations of groups
--
-- The functions of the controlled matchings
--
-- A state of four wires with wire 3 set is a state of the upper half,
-- numbered by the Gray position of its lower wires (enc8, the
-- positions of CFrame and CLabels).  The controlled matching Xm l
-- fixes the lower half and acts on the upper half as the matching of
-- its label (mF l); this is decided for the 105 labels at once
-- (Xm-sem).  Words of labels then act as the products of their
-- matchings (Xs-sem, in LabelEngine's Xs).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CSem where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base using ([] ; _∷_)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics
  using (Bits ; Fun ; ⟦_⟧ ; _≐_ ; _⨾_ ; ⨾-cong ; eqF ; eqF-sound)
open import Examples.Groups.XCXCCX-4bit.CRel using (L ; Xm ; tbl)

private
  ∧ˡ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧ʳ {true} h = h

------------------------------------------------------------------------
-- Finite checks

allFin : (n : ℕ) → (Fin n → Bool) → Bool
allFin zero    p = true
allFin (suc n) p = p zero ∧ allFin n (λ i → p (suc i))

allFin-sound : (n : ℕ) (p : Fin n → Bool) → allFin n p ≡ true → ∀ i → p i ≡ true
allFin-sound (suc n) p h zero    = ∧ˡ h
allFin-sound (suc n) p h (suc i) = allFin-sound n (λ j → p (suc j)) (∧ʳ {p zero} h) i

------------------------------------------------------------------------
-- The upper half

-- The state of the upper half at a Gray position.
enc8 : Fin 8 → Bits 4
enc8 ₀ = false ∷ false ∷ false ∷ true ∷ []
enc8 ₁ = true ∷ false ∷ false ∷ true ∷ []
enc8 ₂ = true ∷ true ∷ false ∷ true ∷ []
enc8 ₃ = false ∷ true ∷ false ∷ true ∷ []
enc8 ₄ = false ∷ true ∷ true ∷ true ∷ []
enc8 ₅ = true ∷ true ∷ true ∷ true ∷ []
enc8 ₆ = true ∷ false ∷ true ∷ true ∷ []
enc8 ₇ = false ∷ false ∷ true ∷ true ∷ []

-- The Gray position of the lower wires of a state.
pos : Bits 4 → Fin 8
pos (false ∷ false ∷ false ∷ _ ∷ []) = ₀
pos (true  ∷ false ∷ false ∷ _ ∷ []) = ₁
pos (true  ∷ true  ∷ false ∷ _ ∷ []) = ₂
pos (false ∷ true  ∷ false ∷ _ ∷ []) = ₃
pos (false ∷ true  ∷ true  ∷ _ ∷ []) = ₄
pos (true  ∷ true  ∷ true  ∷ _ ∷ []) = ₅
pos (true  ∷ false ∷ true  ∷ _ ∷ []) = ₆
pos (false ∷ false ∷ true  ∷ _ ∷ []) = ₇

pos-enc8 : (i : Fin 8) → pos (enc8 i) ≡ i
pos-enc8 ₀ = Eq.refl
pos-enc8 ₁ = Eq.refl
pos-enc8 ₂ = Eq.refl
pos-enc8 ₃ = Eq.refl
pos-enc8 ₄ = Eq.refl
pos-enc8 ₅ = Eq.refl
pos-enc8 ₆ = Eq.refl
pos-enc8 ₇ = Eq.refl

enc8-injective : {i j : Fin 8} → enc8 i ≡ enc8 j → i ≡ j
enc8-injective {i} {j} e = Eq.trans (Eq.sym (pos-enc8 i)) (Eq.trans (Eq.cong pos e) (pos-enc8 j))

------------------------------------------------------------------------
-- The function of a label

-- The matching of the label on the upper half, the identity on the
-- lower half.
mF : L → Fun 4
mF l (a ∷ b ∷ c ∷ false ∷ []) = a ∷ b ∷ c ∷ false ∷ []
mF l (a ∷ b ∷ c ∷ true ∷ [])  = enc8 (tbl l (pos (a ∷ b ∷ c ∷ true ∷ [])))

private
  Xm-sem-ok : allFin 105 (λ l → eqF 4 ⟦ Xm l ⟧ (mF l)) ≡ true
  Xm-sem-ok = Eq.refl

Xm-sem : (l : L) → ⟦ Xm l ⟧ ≐ mF l
Xm-sem l = eqF-sound 4 ⟦ Xm l ⟧ (mF l) (allFin-sound 105 (λ l → eqF 4 ⟦ Xm l ⟧ (mF l)) Xm-sem-ok l)

-- A word of labels, its matchings in diagram order.
mF* : List L → Fun 4
mF* []       = id
mF* (l ∷ ls) = mF l ⨾ mF* ls

mF*-++ : (ls ks : List L) → mF* (ls ++ ks) ≐ (mF* ls ⨾ mF* ks)
mF*-++ []       ks x = Eq.refl
mF*-++ (l ∷ ls) ks x = mF*-++ ls ks (mF l x)
