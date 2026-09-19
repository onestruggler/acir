------------------------------------------------------------------------
-- Presentations of groups
--
-- Auxiliary equations on three qubits (Clément, Lemma D.2)
--
-- Equations (117)–(147) of Appendix D.2, consequences of Figure 4.  A
-- step the paper labels "Lemma 7.6" rewrites a block on two wires by
-- completeness on two qubits: one evaluation through
-- ThreeQubit.Blocks.  The numbered steps are rules of Figure 4 and
-- earlier equations.
--
-- All thirty-one are here.  The derivations follow the paper up to
-- (138) and (141)–(143); the longer ones are organised differently:
-- (139), (140) and (144), (145) by which gates exchange CCZX and CCXZ,
-- and (146), (147) — each says that a word of involutions equals its
-- reverse — by showing the word to be an involution, (146) through a
-- palindrome under P ⊗ P and (147) from (146) by `twist`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; H² ; Z² ; X² ; CZ² ; CH² ; Ex² ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Words of the shape a b a b: WordAlgebra

private
  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The outer gates

-- CZ₂₀ is the outer block of CZ, an involution.
CZ₂₀² : (₃₊ n) ⊢ CZ₂₀ • CZ₂₀ ≈ ε
CZ₂₀² = O-invol CZ CZ²

-- The negated outer CZ of Figure 4 is the outer block of °CZ.
°CZ₂₀-O : (₃₊ n) ⊢ °CZ₂₀ ≈ O °CZ
°CZ₂₀-O {n} = begin
  X ↑ ↑ • CZ₂₀ • X ↑ ↑
    ≈⟨ cong (sym (O-top X)) (back _ (sym (O-top X))) ⟩
  O (X ↑) • O CZ • O (X ↑)
    ≈⟨ back _ (sym (O-• CZ (X ↑))) ⟩
  O (X ↑) • O (CZ • X ↑)
    ≈⟨ sym (O-• (X ↑) (CZ • X ↑)) ⟩
  O (X ↑ • CZ • X ↑) ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- Z below an outer CZ negates its upper control.
Z↓-CZ₂₀ : (₃₊ n) ⊢ Z ↓ • CZ₂₀ ≈ °CZ₂₀
Z↓-CZ₂₀ {n} = begin
  Z ↓ • O CZ         ≈⟨ front _ (sym O-Z↓) ⟩
  O (Z ↓) • O CZ     ≈⟨ sym (O-• (Z ↓) CZ) ⟩
  O (Z ↓ • CZ)       ≈⟨ O-sem (Z ↓ • CZ) °CZ Eq.refl ⟩
  O °CZ              ≈⟨ sym °CZ₂₀-O ⟩
  °CZ₂₀ ∎
  where open Tools ((₃₊ n) VRel,_===_)

CZ₂₀-Z↓ : (₃₊ n) ⊢ °CZ₂₀ ≈ CZ₂₀ • Z ↓
CZ₂₀-Z↓ {n} = begin
  °CZ₂₀              ≈⟨ °CZ₂₀-O ⟩
  O °CZ              ≈⟨ O-sem °CZ (CZ • Z ↓) Eq.refl ⟩
  O (CZ • Z ↓)       ≈⟨ O-• CZ (Z ↓) ⟩
  O CZ • O (Z ↓)     ≈⟨ back _ O-Z↓ ⟩
  CZ₂₀ • Z ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- Z on the top wire passes an outer CZ.
Z↑↑-CZ₂₀ : (₃₊ n) ⊢ Z ↑ ↑ • CZ₂₀ ≈ CZ₂₀ • Z ↑ ↑
Z↑↑-CZ₂₀ {n} = begin
  Z ↑ ↑ • O CZ         ≈⟨ front _ (sym (O-top Z)) ⟩
  O (Z ↑) • O CZ       ≈⟨ sym (O-• (Z ↑) CZ) ⟩
  O (Z ↑ • CZ)         ≈⟨ O-sem (Z ↑ • CZ) (CZ • Z ↑) Eq.refl ⟩
  O (CZ • Z ↑)         ≈⟨ O-• CZ (Z ↑) ⟩
  O CZ • O (Z ↑)       ≈⟨ back _ (O-top Z) ⟩
  CZ₂₀ • Z ↑ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (117)–(126): the doubly-controlled ZX and XZ

-- (117), (118): CCZX and CCXZ are inverse to each other.
eq117 : (₃₊ n) ⊢ CCZX • CCXZ ≈ ε
eq117 {n} = invol-abab CH² CZ₂₀²
  where open Alg ((₃₊ n) VRel,_===_)

eq118 : (₃₊ n) ⊢ CCXZ • CCZX ≈ ε
eq118 {n} = invol-abab CZ₂₀² CH²
  where open Alg ((₃₊ n) VRel,_===_)

-- (119), (120): Z on the middle wire passes them.
eq119 : (₃₊ n) ⊢ Z ↑ • CCZX ≈ CCZX • Z ↑
eq119 {n} = comm-abab (L-sem (Z ↑ • CH) (CH • Z ↑) Eq.refl) (Z↑-O CZ)
  where open Alg ((₃₊ n) VRel,_===_)

eq120 : (₃₊ n) ⊢ Z ↑ • CCXZ ≈ CCXZ • Z ↑
eq120 {n} = comm-abab (Z↑-O CZ) (L-sem (Z ↑ • CH) (CH • Z ↑) Eq.refl)
  where open Alg ((₃₊ n) VRel,_===_)

-- (121), (122): and Z on the top wire.
eq121 : (₃₊ n) ⊢ Z ↑ ↑ • CCZX ≈ CCZX • Z ↑ ↑
eq121 {n} = comm-abab (sym (L-comm CH Z)) Z↑↑-CZ₂₀
  where
  open Alg ((₃₊ n) VRel,_===_)
  open Tools ((₃₊ n) VRel,_===_) using (sym)

eq122 : (₃₊ n) ⊢ Z ↑ ↑ • CCXZ ≈ CCXZ • Z ↑ ↑
eq122 {n} = comm-abab Z↑↑-CZ₂₀ (sym (L-comm CH Z))
  where
  open Alg ((₃₊ n) VRel,_===_)
  open Tools ((₃₊ n) VRel,_===_) using (sym)

-- (123): Z on the target turns CCXZ into CCZX.
eq123 : (₃₊ n) ⊢ Z ↓ • CCXZ ≈ CCZX • Z ↓
eq123 {n} = begin
  Z ↓ • CZ₂₀ • CH • CZ₂₀ • CH
    ≈⟨ by-assoc Eq.refl ⟩
  (Z ↓ • CZ₂₀) • CH • CZ₂₀ • CH
    ≈⟨ front _ Z↓-CZ₂₀ ⟩
  °CZ₂₀ • CH • CZ₂₀ • CH
    ≈⟨ ax comm-°CZ₂₀-CH ⟩
  CH • CZ₂₀ • CH • °CZ₂₀
    ≈⟨ back _ (back _ (back _ CZ₂₀-Z↓)) ⟩
  CH • CZ₂₀ • CH • CZ₂₀ • Z ↓
    ≈⟨ by-assoc Eq.refl ⟩
  CCZX • Z ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (15), as an equation about CCZX.
CCZX² : (₃₊ n) ⊢ CCZX • CCZX ≈ CZ ↑
CCZX² {n} = trans (by-assoc Eq.refl) (ax square-CCZX)
  where open Tools ((₃₊ n) VRel,_===_)

private
  CZ↑² : (₃₊ n) ⊢ CZ ↑ • CZ ↑ ≈ ε
  CZ↑² = lemma-cong↑ (CZ • CZ) ε CZ²

-- (124)
eq124 : (₃₊ n) ⊢ CCZX • CZ ↑ ≈ CCXZ
eq124 {n} = begin
  CCZX • CZ ↑
    ≈⟨ trans (sym left-unit) (trans (front _ (sym eq118)) assoc) ⟩
  CCXZ • CCZX • CCZX • CZ ↑
    ≈⟨ back _ (trans (sym assoc) (front _ CCZX²)) ⟩
  CCXZ • CZ ↑ • CZ ↑
    ≈⟨ cancelᵉ _ CZ↑² ⟩
  CCXZ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (125)
eq125 : (₃₊ n) ⊢ Z ↓ • CCZX ≈ CCZX • CZ ↑ • Z ↓
eq125 {n} = begin
  Z ↓ • CCZX
    ≈⟨ back _ (insertʳ _ CZ↑²) ⟩
  Z ↓ • (CCZX • CZ ↑) • CZ ↑
    ≈⟨ back _ (front _ eq124) ⟩
  Z ↓ • CCXZ • CZ ↑
    ≈⟨ trans (sym assoc) (front _ eq123) ⟩
  (CCZX • Z ↓) • CZ ↑
    ≈⟨ trans assoc (back _ (comm-↓↑ Z CZ)) ⟩
  CCZX • CZ ↑ • Z ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (126)
eq126 : (₃₊ n) ⊢ CCZX • Z ↓ • CCXZ • Z ↓ ≈ CZ ↑
eq126 {n} = begin
  CCZX • Z ↓ • CCXZ • Z ↓
    ≈⟨ back _ (back _ (front _ (sym eq124))) ⟩
  CCZX • Z ↓ • (CCZX • CZ ↑) • Z ↓
    ≈⟨ back _ (back _ assoc) ⟩
  CCZX • Z ↓ • CCZX • CZ ↑ • Z ↓
    ≈⟨ back _ (back _ (sym eq125)) ⟩
  CCZX • Z ↓ • Z ↓ • CCZX
    ≈⟨ back _ (cancelˡ _ Z²) ⟩
  CCZX • CCZX
    ≈⟨ CCZX² ⟩
  CZ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- The swap of the upper pair, and X on the top wire, as conjugations

private
  Ex↑² : (₃₊ n) ⊢ Ex ↑ • Ex ↑ ≈ ε
  Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

  X↑↑² : (₃₊ n) ⊢ X ↑ ↑ • X ↑ ↑ ≈ ε
  X↑↑² = lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)

module S↑ {n : ℕ} = Conj {₃₊ n} (Ex ↑) Ex↑²
module N₂ {n : ℕ} = Conj {₃₊ n} (X ↑ ↑) X↑↑²

-- The swap rules (f3), (f4): the outer gates through the upper swap.
CZ₂₀-Ex↑ : (₃₊ n) ⊢ CZ₂₀ • Ex ↑ ≈ Ex ↑ • CZ ↓
CZ₂₀-Ex↑ {n} = begin
  (Ex ↓ • CZ ↑ • Ex ↓) • Ex ↑   ≈⟨ by-assoc Eq.refl ⟩
  Ex ↓ • (CZ ↑ • Ex ↓ • Ex ↑)   ≈⟨ back _ (ax swap-CZ) ⟩
  Ex ↓ • (Ex ↓ • Ex ↑ • CZ ↓)   ≈⟨ cancelˡ _ Ex² ⟩
  Ex ↑ • CZ ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

CH₂₀-Ex↑ : (₃₊ n) ⊢ CH₂₀ • Ex ↑ ≈ Ex ↑ • CH ↓
CH₂₀-Ex↑ {n} = begin
  (Ex ↓ • CH ↑ • Ex ↓) • Ex ↑   ≈⟨ by-assoc Eq.refl ⟩
  Ex ↓ • (CH ↑ • Ex ↓ • Ex ↑)   ≈⟨ back _ (ax swap-CH) ⟩
  Ex ↓ • (Ex ↓ • Ex ↑ • CH ↓)   ≈⟨ cancelˡ _ Ex² ⟩
  Ex ↑ • CH ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The conjugation table of the upper swap.
S↑-CZ₂₀ : (₃₊ n) ⊢ S↑.⟪ CZ₂₀ ⟫ ≈ CZ ↓
S↑-CZ₂₀ {n} = trans (back _ CZ₂₀-Ex↑) (cancelˡ _ Ex↑²)
  where open Tools ((₃₊ n) VRel,_===_)

S↑-CH₂₀ : (₃₊ n) ⊢ S↑.⟪ CH₂₀ ⟫ ≈ CH ↓
S↑-CH₂₀ {n} = trans (back _ CH₂₀-Ex↑) (cancelˡ _ Ex↑²)
  where open Tools ((₃₊ n) VRel,_===_)

S↑-CZ↓ : (₃₊ n) ⊢ S↑.⟪ CZ ↓ ⟫ ≈ CZ₂₀
S↑-CZ↓ {n} = conj-sym Ex↑² S↑-CZ₂₀
  where open Tools ((₃₊ n) VRel,_===_)

S↑-CH↓ : (₃₊ n) ⊢ S↑.⟪ CH ↓ ⟫ ≈ CH₂₀
S↑-CH↓ {n} = conj-sym Ex↑² S↑-CH₂₀
  where open Tools ((₃₊ n) VRel,_===_)

S↑-CZ↑ : (₃₊ n) ⊢ S↑.⟪ CZ ↑ ⟫ ≈ CZ ↑
S↑-CZ↑ = U-sem (Ex • CZ • Ex) CZ Eq.refl

-- (127): the two controls of CCZX are interchangeable.
eq127 : (₃₊ n) ⊢ CCZX • Ex ↑ ≈ Ex ↑ • CCZX
eq127 {n} = sym (S↑.⟪⟫-comm (trans (S↑.⟪⟫-•₄ S↑-CH↓ S↑-CZ₂₀ S↑-CH↓ S↑-CZ₂₀) (sym (ax symm-controls))))
  where open Tools ((₃₊ n) VRel,_===_)

-- (128)
eq128 : (₃₊ n) ⊢ CZ₂₀ • CCZX ≈ CCZX • CZ ↑ • CZ₂₀
eq128 {n} = begin
  CZ₂₀ • CCZX            ≈⟨ by-assoc Eq.refl ⟩
  CCXZ • CZ₂₀            ≈⟨ front _ (sym eq124) ⟩
  (CCZX • CZ ↑) • CZ₂₀   ≈⟨ assoc ⟩
  CCZX • CZ ↑ • CZ₂₀ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The diagonal gates on different pairs commute: (12) through the
-- upper swap.
CZ↑-CZ₂₀ : (₃₊ n) ⊢ CZ ↑ • CZ₂₀ ≈ CZ₂₀ • CZ ↑
CZ↑-CZ₂₀ {n} = begin
  CZ ↑ • CZ₂₀           ≈⟨ sym (S↑.⟪⟫-•₂ S↑-CZ↑ S↑-CZ↓) ⟩
  S↑.⟪ CZ ↑ • CZ ↓ ⟫     ≈⟨ S↑.⟪⟫-cong (ax comm-CZ↑-CZ↓) ⟩
  S↑.⟪ CZ ↓ • CZ ↑ ⟫     ≈⟨ S↑.⟪⟫-•₂ S↑-CZ↓ S↑-CZ↑ ⟩
  CZ₂₀ • CZ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (131)
eq131 : (₃₊ n) ⊢ U °CZ • CZ₂₀ ≈ CZ₂₀ • U °CZ
eq131 {n} = begin
  U °CZ • CZ₂₀            ≈⟨ front _ (U-sem °CZ (CZ • Z ↓) Eq.refl) ⟩
  (CZ ↑ • Z ↑) • CZ₂₀     ≈⟨ assoc ⟩
  CZ ↑ • Z ↑ • CZ₂₀       ≈⟨ back _ (Z↑-O CZ) ⟩
  CZ ↑ • CZ₂₀ • Z ↑       ≈⟨ trans (sym assoc) (front _ CZ↑-CZ₂₀) ⟩
  (CZ₂₀ • CZ ↑) • Z ↑     ≈⟨ assoc ⟩
  CZ₂₀ • (CZ ↑ • Z ↑)     ≈⟨ back _ (U-sem (CZ • Z ↓) °CZ Eq.refl) ⟩
  CZ₂₀ • U °CZ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (136)–(138): merging a white and a black control

-- CCZX and CCXZ with the top control negated.
°CCZX °CCXZ : Circuit (₃₊ n)
°CCZX = X ↑ ↑ • CCZX • X ↑ ↑
°CCXZ = X ↑ ↑ • CCXZ • X ↑ ↑

private
  -- X on the top wire fixes the lower blocks, and puts Z on the target
  -- of the outer CZ.
  N₂-L : (u : Circuit 2) → (₃₊ n) ⊢ N₂.⟪ L u ⟫ ≈ L u
  N₂-L {n} u = N₂.⟪⟫-fix (sym (L-comm u X))
    where open Tools ((₃₊ n) VRel,_===_)

  Z↓-b : (₃₊ n) ⊢ Z ↓ • CZ₂₀ ≈ CZ₂₀ • Z ↓
  Z↓-b {n} = trans Z↓-CZ₂₀ CZ₂₀-Z↓
    where open Tools ((₃₊ n) VRel,_===_)

  °CCZX-form : (₃₊ n) ⊢ °CCZX ≈ CH • (CZ₂₀ • Z ↓) • CH • (CZ₂₀ • Z ↓)
  °CCZX-form = N₂.⟪⟫-•₄ (N₂-L CH) CZ₂₀-Z↓ (N₂-L CH) CZ₂₀-Z↓

-- The controlled ZX and XZ on the lower pair, written out.
CZX↓ : (₃₊ n) ⊢ L (ΛZX 1) ≈ CH • Z ↓ • CH • Z ↓
CZX↓ = L-sem (ΛZX 1) (CH • Z ↓ • CH • Z ↓) Eq.refl

-- (136)
eq136 : (₃₊ n) ⊢ °CCZX • CCZX ≈ L (ΛZX 1)
eq136 {n} = begin
  °CCZX • CCZX
    ≈⟨ front _ °CCZX-form ⟩
  (CH • (CZ₂₀ • Z ↓) • CH • (CZ₂₀ • Z ↓)) • CCZX
    ≈⟨ merge CH² CZ₂₀² Z↓-b eq123 ⟩
  CH • Z ↓ • CH • Z ↓
    ≈⟨ sym CZX↓ ⟩
  L (ΛZX 1) ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

-- (137): the same in the other order, by conjugating (136) with X on
-- the top wire.
eq137 : (₃₊ n) ⊢ CCZX • °CCZX ≈ L (ΛZX 1)
eq137 {n} = begin
  CCZX • °CCZX            ≈⟨ sym (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CCZX) refl) ⟩
  N₂.⟪ °CCZX • CCZX ⟫     ≈⟨ N₂.⟪⟫-cong eq136 ⟩
  N₂.⟪ L (ΛZX 1) ⟫        ≈⟨ N₂-L (ΛZX 1) ⟩
  L (ΛZX 1) ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (138): the inverses of the two sides of (136).
eq138 : (₃₊ n) ⊢ CCXZ • °CCXZ ≈ L (ΛXZ 1)
eq138 {n} = inv-unique inv (L-sem (ΛXZ 1 • ΛZX 1) ε Eq.refl) eq136
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)
  inv : (₃₊ n) ⊢ (°CCZX • CCZX) • (CCXZ • °CCXZ) ≈ ε
  inv = begin
    (°CCZX • CCZX) • (CCXZ • °CCXZ)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    °CCZX • (CCZX • CCXZ) • °CCXZ
      ≈⟨ back _ (trans (front _ eq117) left-unit) ⟩
    °CCZX • °CCXZ
      ≈⟨ sym (N₂.⟪⟫-• CCZX CCXZ) ⟩
    N₂.⟪ CCZX • CCXZ ⟫
      ≈⟨ N₂.⟪⟫-cong eq117 ⟩
    N₂.⟪ ε ⟫
      ≈⟨ N₂.⟪⟫-ε ⟩
    ε ∎

------------------------------------------------------------------------
-- Conjugation by P ⊗ P on the lower pair, and by the lower swap

private
  PP² : (₃₊ n) ⊢ PP ↓ • PP ↓ ≈ ε
  PP² = L-sem (PP • PP) ε Eq.refl

module PP↓ {n : ℕ} = Conj {₃₊ n} (PP ↓) PP²
module S↓ {n : ℕ} = Conj {₃₊ n} (Ex ↓) Ex²

-- (18): P ⊗ P below turns the upper CZ into the upper CH; it fixes the
-- lower swap, hence turns the outer CZ into the outer CH.
PP-CZ↑ : (₃₊ n) ⊢ PP↓.⟪ CZ ↑ ⟫ ≈ CH ↑
PP-CZ↑ {n} = trans (back _ (ax conj-PP)) (cancelˡ _ PP²)
  where open Tools ((₃₊ n) VRel,_===_)

PP-CH↑ : (₃₊ n) ⊢ PP↓.⟪ CH ↑ ⟫ ≈ CZ ↑
PP-CH↑ {n} = conj-sym PP² PP-CZ↑
  where open Tools ((₃₊ n) VRel,_===_)

PP-Ex↓ : (₃₊ n) ⊢ PP↓.⟪ Ex ↓ ⟫ ≈ Ex ↓
PP-Ex↓ = L-sem (PP • Ex • PP) Ex Eq.refl

PP-CZ₂₀ : (₃₊ n) ⊢ PP↓.⟪ CZ₂₀ ⟫ ≈ CH₂₀
PP-CZ₂₀ = PP↓.⟪⟫-•₃ PP-Ex↓ PP-CZ↑ PP-Ex↓

PP-CH₂₀ : (₃₊ n) ⊢ PP↓.⟪ CH₂₀ ⟫ ≈ CZ₂₀
PP-CH₂₀ {n} = conj-sym PP² PP-CZ₂₀
  where open Tools ((₃₊ n) VRel,_===_)

-- (114), (113): on the lower pair it turns CH upside down and Z on
-- the upper wire into H.
PP-CH↓ : (₃₊ n) ⊢ PP↓.⟪ CH ↓ ⟫ ≈ HC ↓
PP-CH↓ = L-sem (PP • CH • PP) HC Eq.refl

PP-Z↑ : (₃₊ n) ⊢ PP↓.⟪ Z ↑ ⟫ ≈ H ↑
PP-Z↑ = L-sem (PP • Z ↑ • PP) (H ↑) Eq.refl

-- It fixes what lives on the top wire.
PP-top : (v : Circuit (₁₊ n)) → (₃₊ n) ⊢ PP↓.⟪ v ↑ ↑ ⟫ ≈ v ↑ ↑
PP-top v = PP↓.⟪⟫-fix (L-comm PP v)

------------------------------------------------------------------------
-- (132)–(135): controlled H gates sharing a wire

-- The outer CH with its control negated.
°CH₂₀ : Circuit (₃₊ n)
°CH₂₀ = X ↑ ↑ • CH₂₀ • X ↑ ↑

-- X on the top wire around an outer block negates its upper wire.
N₂-O : (u : Circuit 2) → (₃₊ n) ⊢ X ↑ ↑ • O u • X ↑ ↑ ≈ O (X ↑ • u • X ↑)
N₂-O {n} u = begin
  X ↑ ↑ • O u • X ↑ ↑
    ≈⟨ cong (sym (O-top X)) (back _ (sym (O-top X))) ⟩
  O (X ↑) • O u • O (X ↑)
    ≈⟨ back _ (sym (O-• u (X ↑))) ⟩
  O (X ↑) • O (u • X ↑)
    ≈⟨ sym (O-• (X ↑) (u • X ↑)) ⟩
  O (X ↑ • u • X ↑) ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (5), (7) on the outer pair: the negated CH is CH followed by H on
-- the target.
°CH₂₀-form : (₃₊ n) ⊢ °CH₂₀ ≈ CH₂₀ • H ↓
°CH₂₀-form {n} = begin
  °CH₂₀              ≈⟨ N₂-O CH ⟩
  O °CH              ≈⟨ O-sem °CH (CH • H ↓) Eq.refl ⟩
  O (CH • H ↓)       ≈⟨ O-• CH (H ↓) ⟩
  O CH • O (H ↓)     ≈⟨ back _ O-H↓ ⟩
  CH₂₀ • H ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (13) through the upper swap: the upper CZ passes the outer CH.
CZ↑-CH₂₀ : (₃₊ n) ⊢ CZ ↑ • CH₂₀ ≈ CH₂₀ • CZ ↑
CZ↑-CH₂₀ {n} = begin
  CZ ↑ • CH₂₀           ≈⟨ sym (S↑.⟪⟫-•₂ S↑-CZ↑ S↑-CH↓) ⟩
  S↑.⟪ CZ ↑ • CH ↓ ⟫     ≈⟨ S↑.⟪⟫-cong (ax comm-CZ↑-CH↓) ⟩
  S↑.⟪ CH ↓ • CZ ↑ ⟫     ≈⟨ S↑.⟪⟫-•₂ S↑-CH↓ S↑-CZ↑ ⟩
  CH₂₀ • CZ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (132)
eq132 : (₃₊ n) ⊢ CZ ↑ • °CH₂₀ ≈ °CH₂₀ • CZ ↑
eq132 {n} = begin
  CZ ↑ • °CH₂₀            ≈⟨ back _ °CH₂₀-form ⟩
  CZ ↑ • CH₂₀ • H ↓       ≈⟨ trans (sym assoc) (front _ CZ↑-CH₂₀) ⟩
  (CH₂₀ • CZ ↑) • H ↓     ≈⟨ assoc ⟩
  CH₂₀ • CZ ↑ • H ↓       ≈⟨ back _ (sym (comm-↓↑ H CZ)) ⟩
  CH₂₀ • H ↓ • CZ ↑       ≈⟨ sym assoc ⟩
  (CH₂₀ • H ↓) • CZ ↑     ≈⟨ front _ (sym °CH₂₀-form) ⟩
  °CH₂₀ • CZ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (133)
eq133 : (₃₊ n) ⊢ CH ↑ • CH₂₀ ≈ CH₂₀ • CH ↑
eq133 {n} = begin
  CH ↑ • CH₂₀            ≈⟨ sym (PP↓.⟪⟫-•₂ PP-CZ↑ PP-CZ₂₀) ⟩
  PP↓.⟪ CZ ↑ • CZ₂₀ ⟫     ≈⟨ PP↓.⟪⟫-cong CZ↑-CZ₂₀ ⟩
  PP↓.⟪ CZ₂₀ • CZ ↑ ⟫     ≈⟨ PP↓.⟪⟫-•₂ PP-CZ₂₀ PP-CZ↑ ⟩
  CH₂₀ • CH ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The upper CZ passes the negated outer CZ.
CZ↑-°CZ₂₀ : (₃₊ n) ⊢ CZ ↑ • °CZ₂₀ ≈ °CZ₂₀ • CZ ↑
CZ↑-°CZ₂₀ {n} = begin
  CZ ↑ • °CZ₂₀            ≈⟨ back _ CZ₂₀-Z↓ ⟩
  CZ ↑ • CZ₂₀ • Z ↓       ≈⟨ trans (sym assoc) (front _ CZ↑-CZ₂₀) ⟩
  (CZ₂₀ • CZ ↑) • Z ↓     ≈⟨ assoc ⟩
  CZ₂₀ • CZ ↑ • Z ↓       ≈⟨ back _ (sym (comm-↓↑ Z CZ)) ⟩
  CZ₂₀ • Z ↓ • CZ ↑       ≈⟨ sym assoc ⟩
  (CZ₂₀ • Z ↓) • CZ ↑     ≈⟨ front _ (sym CZ₂₀-Z↓) ⟩
  °CZ₂₀ • CZ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

PP-°CZ₂₀ : (₃₊ n) ⊢ PP↓.⟪ °CZ₂₀ ⟫ ≈ °CH₂₀
PP-°CZ₂₀ = PP↓.⟪⟫-•₃ (PP-top X) PP-CZ₂₀ (PP-top X)

-- (134)
eq134 : (₃₊ n) ⊢ CH ↑ • °CH₂₀ ≈ °CH₂₀ • CH ↑
eq134 {n} = begin
  CH ↑ • °CH₂₀            ≈⟨ sym (PP↓.⟪⟫-•₂ PP-CZ↑ PP-°CZ₂₀) ⟩
  PP↓.⟪ CZ ↑ • °CZ₂₀ ⟫     ≈⟨ PP↓.⟪⟫-cong CZ↑-°CZ₂₀ ⟩
  PP↓.⟪ °CZ₂₀ • CZ ↑ ⟫     ≈⟨ PP↓.⟪⟫-•₂ PP-°CZ₂₀ PP-CZ↑ ⟩
  °CH₂₀ • CH ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (13) through the lower swap: the outer CZ passes the lower HC.
CZ₂₀-HC↓ : (₃₊ n) ⊢ CZ₂₀ • HC ↓ ≈ HC ↓ • CZ₂₀
CZ₂₀-HC↓ {n} = begin
  CZ₂₀ • HC ↓            ≈⟨ sym (S↓.⟪⟫-• (CZ ↑) (CH ↓)) ⟩
  S↓.⟪ CZ ↑ • CH ↓ ⟫     ≈⟨ S↓.⟪⟫-cong (ax comm-CZ↑-CH↓) ⟩
  S↓.⟪ CH ↓ • CZ ↑ ⟫     ≈⟨ S↓.⟪⟫-• (CH ↓) (CZ ↑) ⟩
  HC ↓ • CZ₂₀ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- (135): two controlled H gates on one target.
eq135 : (₃₊ n) ⊢ CH₂₀ • CH ↓ ≈ CH ↓ • CH₂₀
eq135 {n} = begin
  CH₂₀ • CH ↓                     ≈⟨ sym (PP↓.⟪⟫-⟪⟫ (CH₂₀ • CH ↓)) ⟩
  PP↓.⟪ PP↓.⟪ CH₂₀ • CH ↓ ⟫ ⟫      ≈⟨ PP↓.⟪⟫-cong (PP↓.⟪⟫-•₂ PP-CH₂₀ PP-CH↓) ⟩
  PP↓.⟪ CZ₂₀ • HC ↓ ⟫              ≈⟨ PP↓.⟪⟫-cong CZ₂₀-HC↓ ⟩
  PP↓.⟪ HC ↓ • CZ₂₀ ⟫              ≈⟨ PP↓.⟪⟫-cong (sym (PP↓.⟪⟫-•₂ PP-CH↓ PP-CH₂₀)) ⟩
  PP↓.⟪ PP↓.⟪ CH ↓ • CH₂₀ ⟫ ⟫      ≈⟨ PP↓.⟪⟫-⟪⟫ (CH ↓ • CH₂₀) ⟩
  CH ↓ • CH₂₀ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (129), (130): P ⊗ P and the gates above it

private
  -- From a conjugation to a commutation, the conjugator leading.
  lead : ∀ {c a b : Circuit (₃₊ n)} → (₃₊ n) ⊢ c • c ≈ ε → (₃₊ n) ⊢ c • a • c ≈ b →
         (₃₊ n) ⊢ c • a ≈ b • c
  lead {n} e h = sym (conj-comm e (conj-sym e h))
    where open Tools ((₃₊ n) VRel,_===_)

-- (129): P ⊗ P below turns the controlled ZX above into the controlled XZ.
eq129 : (₃₊ n) ⊢ PP ↓ • U (ΛZX 1) ≈ U (ΛXZ 1) • PP ↓
eq129 {n} = lead PP² (begin
  PP↓.⟪ U (ΛZX 1) ⟫
    ≈⟨ PP↓.⟪⟫-cong (U-sem (ΛZX 1) (CH • Z ↓ • CH • Z ↓) Eq.refl) ⟩
  PP↓.⟪ CH ↑ • Z ↑ • CH ↑ • Z ↑ ⟫
    ≈⟨ PP↓.⟪⟫-•₄ PP-CH↑ PP-Z↑ PP-CH↑ PP-Z↑ ⟩
  CZ ↑ • H ↑ • CZ ↑ • H ↑
    ≈⟨ U-sem (CZ • H ↓ • CZ • H ↓) (ΛXZ 1) Eq.refl ⟩
  U (ΛXZ 1) ∎)
  where open Tools ((₃₊ n) VRel,_===_)

-- (130): P ⊗ P on the lower pair then on the upper pair is P ⊗ P on the
-- outer pair (through the upper swap).
eq130 : (₃₊ n) ⊢ PP ↓ • PP ↑ ≈ Ex ↑ • PP ↓ • Ex ↑
eq130 {n} = begin
  PP ↓ • PP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (PP ↓ • R) • Ex ↑
    ≈⟨ front _ (lead PP² rounds) ⟩
  (Ex ↑ • PP ↓) • Ex ↑
    ≈⟨ assoc ⟩
  Ex ↑ • PP ↓ • Ex ↑ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  -- The three rounds of P ⊗ P on the upper pair, without its swap.
  R : Circuit (₃₊ n)
  R = CH ↑ • H ↑ ↑ • Z ↑ • CH ↑ • H ↑ ↑ • Z ↑ • CH ↑ • H ↑ ↑ • Z ↑
  rounds : (₃₊ n) ⊢ PP↓.⟪ R ⟫ ≈ Ex ↑
  rounds = begin
    PP↓.⟪ R ⟫
      ≈⟨ PP↓.⟪⟫-•₇ PP-CH↑ (PP-top H) PP-Z↑ PP-CH↑ (PP-top H) PP-Z↑
                    (PP↓.⟪⟫-•₃ PP-CH↑ (PP-top H) PP-Z↑) ⟩
    CZ ↑ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ ↑ • H ↑ • CZ ↑ • H ↑ ↑ • H ↑
      ≈⟨ U-sem (CZ • H ↑ • H ↓ • CZ • H ↑ • H ↓ • CZ • H ↑ • H ↓) Ex Eq.refl ⟩
    Ex ↑ ∎

------------------------------------------------------------------------
-- (141)–(143)

-- (15) for CCXZ, by inverses.
CCXZ² : (₃₊ n) ⊢ CCXZ • CCXZ ≈ CZ ↑
CCXZ² {n} = inv-unique inv CZ↑² CCZX²
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)
  inv : (₃₊ n) ⊢ (CCZX • CCZX) • (CCXZ • CCXZ) ≈ ε
  inv = begin
    (CCZX • CCZX) • (CCXZ • CCXZ)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    CCZX • (CCZX • CCXZ) • CCXZ
      ≈⟨ back _ (trans (front _ eq117) left-unit) ⟩
    CCZX • CCXZ
      ≈⟨ eq117 ⟩
    ε ∎

-- (142): the upper CZ passes a gate controlled by the middle wire.
eq142 : (₃₊ n) ⊢ CZ ↑ • L (ΛZX 1) ≈ L (ΛZX 1) • CZ ↑
eq142 {n} = begin
  CZ ↑ • L (ΛZX 1)
    ≈⟨ back _ CZX↓ ⟩
  CZ ↑ • (CH • Z ↓ • CH • Z ↓)
    ≈⟨ comm-abab (ax comm-CZ↑-CH↓) (sym (comm-↓↑ Z CZ)) ⟩
  (CH • Z ↓ • CH • Z ↓) • CZ ↑
    ≈⟨ front _ (sym CZX↓) ⟩
  L (ΛZX 1) • CZ ↑ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

-- (141)
eq141 : (₃₊ n) ⊢ CCXZ • °CCZX ≈ CZ ↑ • L (ΛZX 1)
eq141 {n} = begin
  CCXZ • °CCZX
    ≈⟨ back _ (trans (sym left-unit) (trans (front _ (sym eq118)) assoc)) ⟩
  CCXZ • CCXZ • CCZX • °CCZX
    ≈⟨ back _ (back _ eq137) ⟩
  CCXZ • CCXZ • L (ΛZX 1)
    ≈⟨ trans (sym assoc) (front _ CCXZ²) ⟩
  CZ ↑ • L (ΛZX 1) ∎
  where open Tools ((₃₊ n) VRel,_===_)

private
  °CCXZ-form : (₃₊ n) ⊢ °CCXZ ≈ °CZ₂₀ • CH • °CZ₂₀ • CH
  °CCXZ-form {n} = N₂.⟪⟫-•₄ refl (N₂-L CH) refl (N₂-L CH)
    where open Tools ((₃₊ n) VRel,_===_)

-- (143)
eq143 : (₃₊ n) ⊢ CZ ↑ • °CCXZ ≈ °CCXZ • CZ ↑
eq143 {n} = begin
  CZ ↑ • °CCXZ
    ≈⟨ back _ °CCXZ-form ⟩
  CZ ↑ • (°CZ₂₀ • CH • °CZ₂₀ • CH)
    ≈⟨ comm-abab CZ↑-°CZ₂₀ (ax comm-CZ↑-CH↓) ⟩
  (°CZ₂₀ • CH • °CZ₂₀ • CH) • CZ ↑
    ≈⟨ front _ (sym °CCXZ-form) ⟩
  °CCXZ • CZ ↑ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (139), (140): CCZX and the doubly-controlled gate on the middle wire
--
-- The gate with its target on the middle wire, a white control on top
-- and a black one at the bottom is the conjugate of °CCZX (or °CCXZ)
-- by the lower swap.  The paper's two-page derivation comes down to
-- two facts: the lower CZ turns CCZX into CCXZ (from (123)), and the
-- upper CH passes °CCZX and °CCXZ (from (17)).

-- ZX and XZ on the middle wire, controlled by ○ top and ● bottom.
°CZXC °CXZC : Circuit (₃₊ n)
°CZXC = S↓.⟪ °CCZX ⟫
°CXZC = S↓.⟪ °CCXZ ⟫

private
  CZ↓² : (₃₊ n) ⊢ CZ ↓ • CZ ↓ ≈ ε
  CZ↓² = CZ²

  Z↓² : (₃₊ n) ⊢ Z ↓ • Z ↓ ≈ ε
  Z↓² = Z²

module K {n : ℕ} = Conj {₃₊ n} (CZ ↓) CZ↓²
module Zc {n : ℕ} = Conj {₃₊ n} (Z ↓) Z↓²

-- The lower CZ passes the outer CZ: (12) through the lower swap.
CZ₂₀-CZ↓ : (₃₊ n) ⊢ CZ₂₀ • CZ ↓ ≈ CZ ↓ • CZ₂₀
CZ₂₀-CZ↓ {n} = begin
  CZ₂₀ • CZ ↓
    ≈⟨ back _ (sym sw) ⟩
  S↓.⟪ CZ ↑ ⟫ • S↓.⟪ CZ ↓ ⟫
    ≈⟨ sym (S↓.⟪⟫-• (CZ ↑) (CZ ↓)) ⟩
  S↓.⟪ CZ ↑ • CZ ↓ ⟫
    ≈⟨ S↓.⟪⟫-cong (ax comm-CZ↑-CZ↓) ⟩
  S↓.⟪ CZ ↓ • CZ ↑ ⟫
    ≈⟨ S↓.⟪⟫-• (CZ ↓) (CZ ↑) ⟩
  S↓.⟪ CZ ↓ ⟫ • S↓.⟪ CZ ↑ ⟫
    ≈⟨ front _ sw ⟩
  CZ ↓ • CZ₂₀ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  sw : (₃₊ n) ⊢ S↓.⟪ CZ ↓ ⟫ ≈ CZ ↓
  sw = L-sem (Ex • CZ • Ex) CZ Eq.refl

private
  -- The lower CH with Z around its target.
  a′ : Circuit (₃₊ n)
  a′ = Z ↓ • CH • Z ↓

  K-a : (₃₊ n) ⊢ K.⟪ CH ↓ ⟫ ≈ a′
  K-a = L-sem (CZ • CH • CZ) (Z ↓ • CH • Z ↓) Eq.refl

  K-b : (₃₊ n) ⊢ K.⟪ CZ₂₀ ⟫ ≈ CZ₂₀
  K-b {n} = K.⟪⟫-fix (sym CZ₂₀-CZ↓)
    where open Tools ((₃₊ n) VRel,_===_)

  Zc-b : (₃₊ n) ⊢ Zc.⟪ CZ₂₀ ⟫ ≈ CZ₂₀
  Zc-b = Zc.⟪⟫-fix Z↓-b

  -- (123) as a conjugation: Z around CCXZ is CCZX.
  Zc-V : (₃₊ n) ⊢ Zc.⟪ CCXZ ⟫ ≈ CCZX
  Zc-V {n} = begin
    Z ↓ • CCXZ • Z ↓       ≈⟨ sym assoc ⟩
    (Z ↓ • CCXZ) • Z ↓     ≈⟨ front _ eq123 ⟩
    (CCZX • Z ↓) • Z ↓     ≈⟨ cancelʳ _ Z↓² ⟩
    CCZX ∎
    where open Tools ((₃₊ n) VRel,_===_)

  -- Hence b a′ b a′ = a b a b, and a′ b a′ b = b a b a.
  star : (₃₊ n) ⊢ CZ₂₀ • a′ • CZ₂₀ • a′ ≈ CCZX
  star {n} = trans (sym (Zc.⟪⟫-•₄ Zc-b refl Zc-b refl)) Zc-V
    where open Tools ((₃₊ n) VRel,_===_)

  star′ : (₃₊ n) ⊢ a′ • CZ₂₀ • a′ • CZ₂₀ ≈ CCXZ
  star′ {n} = begin
    a′ • CZ₂₀ • a′ • CZ₂₀
      ≈⟨ insertˡ _ CZ₂₀² ⟩
    CZ₂₀ • CZ₂₀ • a′ • CZ₂₀ • a′ • CZ₂₀
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    CZ₂₀ • (CZ₂₀ • a′ • CZ₂₀ • a′) • CZ₂₀
      ≈⟨ back _ (front _ star) ⟩
    CZ₂₀ • CCZX • CZ₂₀
      ≈⟨ by-assoc Eq.refl ⟩
    CCXZ • (CZ₂₀ • CZ₂₀)
      ≈⟨ cancelᵉ _ CZ₂₀² ⟩
    CCXZ ∎
    where open Tools ((₃₊ n) VRel,_===_)

-- The lower CZ turns CCZX into CCXZ, and back.
K-W : (₃₊ n) ⊢ K.⟪ CCZX ⟫ ≈ CCXZ
K-W {n} = trans (K.⟪⟫-•₄ K-a K-b K-a K-b) star′
  where open Tools ((₃₊ n) VRel,_===_)

K-V : (₃₊ n) ⊢ K.⟪ CCXZ ⟫ ≈ CCZX
K-V {n} = conj-sym CZ↓² K-W
  where open Tools ((₃₊ n) VRel,_===_)

-- The upper CH passes the negated outer CZ: (13) through both swaps.
CH↑-CZ₂₀ : (₃₊ n) ⊢ CH ↑ • CZ₂₀ ≈ CZ₂₀ • CH ↑
CH↑-CZ₂₀ {n} = begin
  CH ↑ • CZ₂₀
    ≈⟨ front _ (sym (S↓.⟪⟫-⟪⟫ (CH ↑))) ⟩
  S↓.⟪ CH₂₀ ⟫ • S↓.⟪ CZ ↑ ⟫
    ≈⟨ sym (S↓.⟪⟫-• CH₂₀ (CZ ↑)) ⟩
  S↓.⟪ CH₂₀ • CZ ↑ ⟫
    ≈⟨ S↓.⟪⟫-cong (sym CZ↑-CH₂₀) ⟩
  S↓.⟪ CZ ↑ • CH₂₀ ⟫
    ≈⟨ S↓.⟪⟫-• (CZ ↑) CH₂₀ ⟩
  S↓.⟪ CZ ↑ ⟫ • S↓.⟪ CH₂₀ ⟫
    ≈⟨ back _ (S↓.⟪⟫-⟪⟫ (CH ↑)) ⟩
  CZ₂₀ • CH ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

private
  t°b : (₃₊ n) ⊢ CH ↑ • °CZ₂₀ ≈ °CZ₂₀ • CH ↑
  t°b {n} = begin
    CH ↑ • °CZ₂₀            ≈⟨ back _ CZ₂₀-Z↓ ⟩
    CH ↑ • CZ₂₀ • Z ↓       ≈⟨ trans (sym assoc) (front _ CH↑-CZ₂₀) ⟩
    (CZ₂₀ • CH ↑) • Z ↓     ≈⟨ assoc ⟩
    CZ₂₀ • CH ↑ • Z ↓       ≈⟨ back _ (sym (comm-↓↑ Z CH)) ⟩
    CZ₂₀ • Z ↓ • CH ↑       ≈⟨ sym assoc ⟩
    (CZ₂₀ • Z ↓) • CH ↑     ≈⟨ front _ (sym CZ₂₀-Z↓) ⟩
    °CZ₂₀ • CH ↑ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  -- (17), with the two lower CH gates moved to the other side.
  t-a°ba : (₃₊ n) ⊢ CH ↑ • CH ↓ • °CZ₂₀ • CH ↓ ≈ CH ↓ • °CZ₂₀ • CH ↓ • CH ↑
  t-a°ba {n} = begin
    CH ↑ • CH ↓ • °CZ₂₀ • CH ↓
      ≈⟨ insertˡ _ CH² ⟩
    CH ↓ • CH ↓ • CH ↑ • CH ↓ • °CZ₂₀ • CH ↓
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    CH ↓ • (CH ↓ • CH ↑ • CH ↓ • °CZ₂₀) • CH ↓
      ≈⟨ back _ (front _ (sym (ax comm-°CZ₂₀-HH))) ⟩
    CH ↓ • (°CZ₂₀ • CH ↓ • CH ↑ • CH ↓) • CH ↓
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
    CH ↓ • °CZ₂₀ • CH ↓ • CH ↑ • (CH ↓ • CH ↓)
      ≈⟨ back _ (back _ (back _ (cancelᵉ _ CH²))) ⟩
    CH ↓ • °CZ₂₀ • CH ↓ • CH ↑ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  °CCZX-form′ : (₃₊ n) ⊢ °CCZX ≈ CH • °CZ₂₀ • CH • °CZ₂₀
  °CCZX-form′ {n} = N₂.⟪⟫-•₄ (N₂-L CH) refl (N₂-L CH) refl
    where open Tools ((₃₊ n) VRel,_===_)

-- The upper CH passes °CCZX and °CCXZ.
CH↑-°CCZX : (₃₊ n) ⊢ CH ↑ • °CCZX ≈ °CCZX • CH ↑
CH↑-°CCZX {n} = begin
  CH ↑ • °CCZX
    ≈⟨ back _ °CCZX-form′ ⟩
  CH ↑ • CH • °CZ₂₀ • CH • °CZ₂₀
    ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (CH ↑ • CH • °CZ₂₀ • CH) • °CZ₂₀
    ≈⟨ front _ t-a°ba ⟩
  (CH • °CZ₂₀ • CH • CH ↑) • °CZ₂₀
    ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  CH • °CZ₂₀ • CH • (CH ↑ • °CZ₂₀)
    ≈⟨ back _ (back _ (back _ t°b)) ⟩
  CH • °CZ₂₀ • CH • (°CZ₂₀ • CH ↑)
    ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (CH • °CZ₂₀ • CH • °CZ₂₀) • CH ↑
    ≈⟨ front _ (sym °CCZX-form′) ⟩
  °CCZX • CH ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

CH↑-°CCXZ : (₃₊ n) ⊢ CH ↑ • °CCXZ ≈ °CCXZ • CH ↑
CH↑-°CCXZ {n} = begin
  CH ↑ • °CCXZ
    ≈⟨ back _ °CCXZ-form ⟩
  CH ↑ • °CZ₂₀ • CH • °CZ₂₀ • CH
    ≈⟨ trans (sym assoc) (front _ t°b) ⟩
  (°CZ₂₀ • CH ↑) • CH • °CZ₂₀ • CH
    ≈⟨ assoc ⟩
  °CZ₂₀ • (CH ↑ • CH • °CZ₂₀ • CH)
    ≈⟨ back _ t-a°ba ⟩
  °CZ₂₀ • (CH • °CZ₂₀ • CH • CH ↑)
    ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (°CZ₂₀ • CH • °CZ₂₀ • CH) • CH ↑
    ≈⟨ front _ (sym °CCXZ-form) ⟩
  °CCXZ • CH ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

private
  -- The lower CZ exchanges the two gates on the middle wire.
  K-top : (v : Circuit (₁₊ n)) → (₃₊ n) ⊢ K.⟪ v ↑ ↑ ⟫ ≈ v ↑ ↑
  K-top v = K.⟪⟫-fix (L-comm CZ v)

  S↓-CZ↓ : (₃₊ n) ⊢ S↓.⟪ CZ ↓ ⟫ ≈ CZ ↓
  S↓-CZ↓ = L-sem (Ex • CZ • Ex) CZ Eq.refl

  K-G : (₃₊ n) ⊢ K.⟪ °CZXC ⟫ ≈ °CXZC
  K-G {n} = begin
    CZ ↓ • S↓.⟪ °CCZX ⟫ • CZ ↓
      ≈⟨ sym (S↓.⟪⟫-•₃ S↓-CZ↓ refl S↓-CZ↓) ⟩
    S↓.⟪ CZ ↓ • °CCZX • CZ ↓ ⟫
      ≈⟨ S↓.⟪⟫-cong (K.⟪⟫-•₃ (K-top X) K-W (K-top X)) ⟩
    S↓.⟪ °CCXZ ⟫ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  K-G′ : (₃₊ n) ⊢ K.⟪ °CXZC ⟫ ≈ °CZXC
  K-G′ {n} = conj-sym CZ↓² K-G
    where open Tools ((₃₊ n) VRel,_===_)

  -- The outer CH passes them.
  p-G : (₃₊ n) ⊢ CH₂₀ • °CZXC ≈ °CZXC • CH₂₀
  p-G {n} = begin
    CH₂₀ • S↓.⟪ °CCZX ⟫       ≈⟨ sym (S↓.⟪⟫-• (CH ↑) °CCZX) ⟩
    S↓.⟪ CH ↑ • °CCZX ⟫       ≈⟨ S↓.⟪⟫-cong CH↑-°CCZX ⟩
    S↓.⟪ °CCZX • CH ↑ ⟫       ≈⟨ S↓.⟪⟫-• °CCZX (CH ↑) ⟩
    S↓.⟪ °CCZX ⟫ • CH₂₀ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  p-G′ : (₃₊ n) ⊢ CH₂₀ • °CXZC ≈ °CXZC • CH₂₀
  p-G′ {n} = begin
    CH₂₀ • S↓.⟪ °CCXZ ⟫       ≈⟨ sym (S↓.⟪⟫-• (CH ↑) °CCXZ) ⟩
    S↓.⟪ CH ↑ • °CCXZ ⟫       ≈⟨ S↓.⟪⟫-cong CH↑-°CCXZ ⟩
    S↓.⟪ °CCXZ • CH ↑ ⟫       ≈⟨ S↓.⟪⟫-• °CCXZ (CH ↑) ⟩
    S↓.⟪ °CCXZ ⟫ • CH₂₀ ∎
    where open Tools ((₃₊ n) VRel,_===_)

-- (139), (140)
eq139 : (₃₊ n) ⊢ CCZX • °CZXC ≈ °CZXC • CCZX
eq139 {n} = begin
  CCZX • °CZXC
    ≈⟨ front _ (ax symm-controls) ⟩
  (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • °CZXC
    ≈⟨ pass-pqpq p-G p-G′ (lead CZ↓² K-G) (lead CZ↓² K-G′) ⟩
  °CZXC • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)
    ≈⟨ back _ (sym (ax symm-controls)) ⟩
  °CZXC • CCZX ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

eq140 : (₃₊ n) ⊢ CCZX • °CXZC ≈ °CXZC • CCZX
eq140 {n} = begin
  CCZX • °CXZC
    ≈⟨ front _ (ax symm-controls) ⟩
  (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • °CXZC
    ≈⟨ pass-pqpq p-G′ p-G (lead CZ↓² K-G′) (lead CZ↓² K-G) ⟩
  °CXZC • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)
    ≈⟨ back _ (sym (ax symm-controls)) ⟩
  °CXZC • CCZX ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (144): H Z on the target passes the doubly controlled ZX

private
  X↑² : (₃₊ n) ⊢ X ↑ • X ↑ ≈ ε
  X↑² = lemma-cong↑ (X • X) ε X²

-- X on the middle wire, as a conjugation.
module N₁ {n : ℕ} = Conj {₃₊ n} (X ↑) X↑²

private
  CH₂₀² : (₃₊ n) ⊢ CH₂₀ • CH₂₀ ≈ ε
  CH₂₀² = O-invol CH CH²

  -- CCXZ with the roles of the two controls exchanged.
  CCXZ-alt : (₃₊ n) ⊢ CCXZ ≈ CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀
  CCXZ-alt {n} = begin
    CCXZ
      ≈⟨ sym K-W ⟩
    CZ ↓ • CCZX • CZ ↓
      ≈⟨ back _ (front _ (ax symm-controls)) ⟩
    CZ ↓ • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • CZ ↓
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
    CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀ • (CZ ↓ • CZ ↓)
      ≈⟨ back _ (back _ (back _ (cancelᵉ _ CZ↓²))) ⟩
    CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  -- H on the target is the two lower controlled H gates.
  h-split : (₃₊ n) ⊢ H ↓ ≈ CH • °CH
  h-split = L-sem (H ↓) (CH • °CH) Eq.refl

  -- The negated lower CH passes the lower CZ and the outer CH.
  °a-q : (₃₊ n) ⊢ °CH ↓ • CZ ↓ ≈ CZ ↓ • °CH ↓
  °a-q = L-sem (°CH • CZ) (CZ • °CH) Eq.refl

  N₁-p : (₃₊ n) ⊢ N₁.⟪ CH₂₀ ⟫ ≈ CH₂₀
  N₁-p = N₁.⟪⟫-fix (X↑-O CH)

  °a-p : (₃₊ n) ⊢ °CH ↓ • CH₂₀ ≈ CH₂₀ • °CH ↓
  °a-p {n} = N₁.⟪⟫-≈ (sym eq135) (N₁.⟪⟫-•₂ refl N₁-p) (N₁.⟪⟫-•₂ N₁-p refl)
    where open Tools ((₃₊ n) VRel,_===_)

  -- So it passes both doubly controlled gates.
  °a-V : (₃₊ n) ⊢ °CH ↓ • CCXZ ≈ CCXZ • °CH ↓
  °a-V {n} = begin
    °CH ↓ • CCXZ                          ≈⟨ back _ CCXZ-alt ⟩
    °CH ↓ • (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀)   ≈⟨ comm-abab °a-q °a-p ⟩
    (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀) • °CH ↓   ≈⟨ front _ (sym CCXZ-alt) ⟩
    CCXZ • °CH ↓ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)

  °a-W : (₃₊ n) ⊢ °CH ↓ • CCZX ≈ CCZX • °CH ↓
  °a-W {n} = begin
    °CH ↓ • CCZX                          ≈⟨ back _ (ax symm-controls) ⟩
    °CH ↓ • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)   ≈⟨ comm-abab °a-p °a-q ⟩
    (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • °CH ↓   ≈⟨ front _ (sym (ax symm-controls)) ⟩
    CCZX • °CH ↓ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)

  -- The gates on the lower pair that exchange CCZX and CCXZ.
  a-W : (₃₊ n) ⊢ CH • CCZX ≈ CCXZ • CH
  a-W {n} = begin
    CH • CCZX                      ≈⟨ cancelˡ _ CH² ⟩
    CZ₂₀ • CH • CZ₂₀               ≈⟨ sym (back _ (back _ (cancelᵉ _ CH²))) ⟩
    CZ₂₀ • CH • CZ₂₀ • (CH • CH)   ≈⟨ by-assoc Eq.refl ⟩
    CCXZ • CH ∎
    where open Tools ((₃₊ n) VRel,_===_)

  a-V : (₃₊ n) ⊢ CH • CCXZ ≈ CCZX • CH
  a-V {n} = by-assoc Eq.refl
    where open Tools ((₃₊ n) VRel,_===_)

  q-W : (₃₊ n) ⊢ CZ ↓ • CCZX ≈ CCXZ • CZ ↓
  q-W = lead CZ↓² K-W

  q-V : (₃₊ n) ⊢ CZ ↓ • CCXZ ≈ CCZX • CZ ↓
  q-V = lead CZ↓² K-V

  z-W : (₃₊ n) ⊢ Z ↓ • CCZX ≈ CCXZ • Z ↓
  z-W {n} = lead Z↓² (conj-sym Z↓² Zc-V)
    where open Tools ((₃₊ n) VRel,_===_)

  h-V : (₃₊ n) ⊢ H ↓ • CCXZ ≈ CCZX • H ↓
  h-V {n} = begin
    H ↓ • CCXZ           ≈⟨ front _ h-split ⟩
    (CH • °CH) • CCXZ    ≈⟨ assoc ⟩
    CH • °CH • CCXZ      ≈⟨ back _ °a-V ⟩
    CH • CCXZ • °CH      ≈⟨ by-assoc Eq.refl ⟩
    CCZX • CH • °CH      ≈⟨ back _ (sym h-split) ⟩
    CCZX • H ↓ ∎
    where open Tools ((₃₊ n) VRel,_===_)

-- (144)
eq144 : (₃₊ n) ⊢ H ↓ • Z ↓ • CCZX ≈ CCZX • H ↓ • Z ↓
eq144 {n} = begin
  H ↓ • Z ↓ • CCZX     ≈⟨ back _ z-W ⟩
  H ↓ • CCXZ • Z ↓     ≈⟨ sym assoc ⟩
  (H ↓ • CCXZ) • Z ↓   ≈⟨ front _ h-V ⟩
  (CCZX • H ↓) • Z ↓   ≈⟨ assoc ⟩
  CCZX • H ↓ • Z ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (145): the controlled H Z passes the controlled ZX on the same target

-- On the target wire 0: the controlled ZX from wire 2 is the two doubly
-- controlled ZX gates, wire 1 black and white, and the controlled H Z
-- from wire 1 passes each.  The swap of the lower pair then puts the
-- target on wire 1.
private
  W° : Circuit (₃₊ n)
  W° = N₁.⟪ CCZX ⟫

  q°-form : (₃₊ n) ⊢ °CZ ↓ ≈ CZ ↓ • Z ↓
  q°-form = L-sem °CZ (CZ • Z ↓) Eq.refl

  aq-W : (₃₊ n) ⊢ (CH • CZ ↓) • CCZX ≈ CCZX • (CH • CZ ↓)
  aq-W {n} = pass-xy q-W a-V
    where open Alg ((₃₊ n) VRel,_===_)

  q°-W : (₃₊ n) ⊢ °CZ ↓ • CCZX ≈ CCZX • °CZ ↓
  q°-W {n} = begin
    °CZ ↓ • CCZX           ≈⟨ front _ q°-form ⟩
    (CZ ↓ • Z ↓) • CCZX    ≈⟨ pass-xy z-W q-V ⟩
    CCZX • (CZ ↓ • Z ↓)    ≈⟨ back _ (sym q°-form) ⟩
    CCZX • °CZ ↓ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)

  °aq-W : (₃₊ n) ⊢ (°CH ↓ • °CZ ↓) • CCZX ≈ CCZX • (°CH ↓ • °CZ ↓)
  °aq-W {n} = pass-xy q°-W °a-W
    where open Alg ((₃₊ n) VRel,_===_)

  aq-W° : (₃₊ n) ⊢ (CH • CZ ↓) • W° ≈ W° • (CH • CZ ↓)
  aq-W° {n} = N₁.⟪⟫-≈ °aq-W
    (N₁.⟪⟫-•₂ (N₁.⟪⟫-•₂ (N₁.⟪⟫-⟪⟫ CH) (N₁.⟪⟫-⟪⟫ (CZ ↓))) refl)
    (N₁.⟪⟫-•₂ refl (N₁.⟪⟫-•₂ (N₁.⟪⟫-⟪⟫ CH) (N₁.⟪⟫-⟪⟫ (CZ ↓))))
    where open Tools ((₃₊ n) VRel,_===_)

  -- The two doubly controlled gates make the controlled ZX from wire 2.
  W°W : (₃₊ n) ⊢ W° • CCZX ≈ CH₂₀ • Z ↓ • CH₂₀ • Z ↓
  W°W {n} = begin
    W° • CCZX
      ≈⟨ cong (N₁.⟪⟫-cong (ax symm-controls)) (ax symm-controls) ⟩
    N₁.⟪ CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓ ⟫ • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)
      ≈⟨ front _ (N₁.⟪⟫-•₄ N₁-p q°-form N₁-p q°-form) ⟩
    (CH₂₀ • (CZ ↓ • Z ↓) • CH₂₀ • (CZ ↓ • Z ↓)) • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)
      ≈⟨ merge CH₂₀² CZ↓² zq h ⟩
    CH₂₀ • Z ↓ • CH₂₀ • Z ↓ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)
    zq : (₃₊ n) ⊢ Z ↓ • CZ ↓ ≈ CZ ↓ • Z ↓
    zq = L-sem (Z ↓ • CZ) (CZ • Z ↓) Eq.refl
    h : (₃₊ n) ⊢ Z ↓ • (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀) ≈ (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • Z ↓
    h = begin
      Z ↓ • (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀)   ≈⟨ back _ (sym CCXZ-alt) ⟩
      Z ↓ • CCXZ                           ≈⟨ eq123 ⟩
      CCZX • Z ↓                           ≈⟨ front _ (ax symm-controls) ⟩
      (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • Z ↓ ∎

  O-CZX : (₃₊ n) ⊢ O (ΛZX 1) ≈ CH₂₀ • Z ↓ • CH₂₀ • Z ↓
  O-CZX {n} = begin
    O (ΛZX 1)                          ≈⟨ O-sem (ΛZX 1) (CH • Z ↓ • CH • Z ↓) Eq.refl ⟩
    O (CH • Z ↓ • CH • Z ↓)            ≈⟨ O-• CH (Z ↓ • CH • Z ↓) ⟩
    O CH • O (Z ↓ • CH • Z ↓)          ≈⟨ back _ (O-• (Z ↓) (CH • Z ↓)) ⟩
    O CH • O (Z ↓) • O (CH • Z ↓)      ≈⟨ back _ (back _ (O-• CH (Z ↓))) ⟩
    O CH • O (Z ↓) • O CH • O (Z ↓)    ≈⟨ back _ (cong O-Z↓ (back _ O-Z↓)) ⟩
    CH₂₀ • Z ↓ • CH₂₀ • Z ↓ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  aq-O : (₃₊ n) ⊢ (CH • CZ ↓) • O (ΛZX 1) ≈ O (ΛZX 1) • (CH • CZ ↓)
  aq-O {n} = begin
    (CH • CZ ↓) • O (ΛZX 1)    ≈⟨ back _ (trans O-CZX (sym W°W)) ⟩
    (CH • CZ ↓) • (W° • CCZX)  ≈⟨ comm-• aq-W° aq-W ⟩
    (W° • CCZX) • (CH • CZ ↓)  ≈⟨ front _ (trans W°W (sym O-CZX)) ⟩
    O (ΛZX 1) • (CH • CZ ↓) ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)

-- (145)
eq145 : (₃₊ n) ⊢ HC ↓ • CZ ↓ • U (ΛZX 1) ≈ U (ΛZX 1) • HC ↓ • CZ ↓
eq145 {n} = begin
  HC ↓ • CZ ↓ • U (ΛZX 1)
    ≈⟨ sym assoc ⟩
  (HC ↓ • CZ ↓) • U (ΛZX 1)
    ≈⟨ S↓.⟪⟫-≈ aq-O
         (S↓.⟪⟫-•₂ (S↓.⟪⟫-•₂ refl S↓-CZ↓) (S↓.⟪⟫-⟪⟫ (U (ΛZX 1))))
         (S↓.⟪⟫-•₂ (S↓.⟪⟫-⟪⟫ (U (ΛZX 1))) (S↓.⟪⟫-•₂ refl S↓-CZ↓)) ⟩
  U (ΛZX 1) • (HC ↓ • CZ ↓) ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (146): a word of involutions equal to its reverse, that is, itself an
-- involution

-- With the X on the top wire pulled out, and the Z it leaves there, the
-- word is T below; P ⊗ P on the lower pair and (14) on the target wire 1
-- turn T into a palindrome.
private
  T Pal : Circuit (₃₊ n)
  T   = CH ↑ • CZ ↑ • CH ↓ • CH ↑ • CH ↓
  Pal = CZ ↑ • (CZ ↓ • CH ↑ • CZ ↓) • CZ ↑

  CH↑² : (₃₊ n) ⊢ CH ↑ • CH ↑ ≈ ε
  CH↑² = lemma-cong↑ (CH • CH) ε CH²

  -- (14) with the target on wire 1.
  symm-controls₁ : (₃₊ n) ⊢ HC ↓ • CZ ↑ • HC ↓ • CZ ↑ ≈ CH ↑ • CZ ↓ • CH ↑ • CZ ↓
  symm-controls₁ {n} = S↓.⟪⟫-≈ (ax symm-controls)
    (S↓.⟪⟫-•₄ refl (S↓.⟪⟫-⟪⟫ (CZ ↑)) refl (S↓.⟪⟫-⟪⟫ (CZ ↑)))
    (S↓.⟪⟫-•₄ (S↓.⟪⟫-⟪⟫ (CH ↑)) S↓-CZ↓ (S↓.⟪⟫-⟪⟫ (CH ↑)) S↓-CZ↓)
    where open Tools ((₃₊ n) VRel,_===_)

  PP-T : (₃₊ n) ⊢ PP↓.⟪ T ⟫ ≈ Pal
  PP-T {n} = begin
    PP↓.⟪ T ⟫
      ≈⟨ PP↓.⟪⟫-•₅ PP-CH↑ PP-CZ↑ PP-CH↓ PP-CH↑ PP-CH↓ ⟩
    CZ ↑ • CH ↑ • HC ↓ • CZ ↑ • HC ↓
      ≈⟨ back _ (back _ (back _ (back _ (insertʳ _ CZ↑²)))) ⟩
    CZ ↑ • CH ↑ • HC ↓ • CZ ↑ • (HC ↓ • CZ ↑) • CZ ↑
      ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □) • □) (□ • □ • (□ • □ • □ • □) • □) Eq.refl ⟩
    CZ ↑ • CH ↑ • (HC ↓ • CZ ↑ • HC ↓ • CZ ↑) • CZ ↑
      ≈⟨ back _ (back _ (front _ symm-controls₁)) ⟩
    CZ ↑ • CH ↑ • (CH ↑ • CZ ↓ • CH ↑ • CZ ↓) • CZ ↑
      ≈⟨ by-passoc (□ • □ • (□ • □ • □ • □) • □) (□ • (□ • □) • (□ • □ • □) • □) Eq.refl ⟩
    CZ ↑ • (CH ↑ • CH ↑) • (CZ ↓ • CH ↑ • CZ ↓) • CZ ↑
      ≈⟨ back _ (cancelˢ _ CH↑²) ⟩
    CZ ↑ • (CZ ↓ • CH ↑ • CZ ↓) • CZ ↑ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  T² : (₃₊ n) ⊢ T • T ≈ ε
  T² {n} = begin
    T • T                         ≈⟨ cong (sym e) (sym e) ⟩
    PP↓.⟪ Pal ⟫ • PP↓.⟪ Pal ⟫     ≈⟨ PP↓.⟪⟫-invol (conj-invol CZ↑² (conj-invol CZ↓² CH↑²)) ⟩
    ε ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    e : (₃₊ n) ⊢ PP↓.⟪ Pal ⟫ ≈ T
    e = conj-sym PP² PP-T

  -- Z on the top wire passes T.
  ζ-T : (₃₊ n) ⊢ Z ↑ ↑ • T ≈ T • Z ↑ ↑
  ζ-T {n} = comm-• t (comm-• c (comm-• a (comm-• t a)))
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)
    t : (₃₊ n) ⊢ Z ↑ ↑ • CH ↑ ≈ CH ↑ • Z ↑ ↑
    t = U-sem (Z ↑ • CH) (CH • Z ↑) Eq.refl
    c : (₃₊ n) ⊢ Z ↑ ↑ • CZ ↑ ≈ CZ ↑ • Z ↑ ↑
    c = U-sem (Z ↑ • CZ) (CZ • Z ↑) Eq.refl
    a : (₃₊ n) ⊢ Z ↑ ↑ • CH ↓ ≈ CH ↓ • Z ↑ ↑
    a = sym (L-comm CH Z)

  Z↑↑² : (₃₊ n) ⊢ Z ↑ ↑ • Z ↑ ↑ ≈ ε
  Z↑↑² = lemma-cong↑ (Z ↑ • Z ↑) ε (lemma-cong↑ (Z • Z) ε Z²)

  -- The negated lower CH around the upper CH.
  °a-t-°a : (₃₊ n) ⊢ °CH ↓ • CH ↑ • °CH ↓ ≈ CH ↓ • CH ↑ • CH ↓
  °a-t-°a {n} = begin
    °CH ↓ • CH ↑ • °CH ↓
      ≈⟨ cong (L-sem °CH (CH • H ↓) Eq.refl) (back _ (L-sem °CH (H ↓ • CH) Eq.refl)) ⟩
    (CH • H ↓) • CH ↑ • (H ↓ • CH)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    CH • (H ↓ • CH ↑) • H ↓ • CH
      ≈⟨ back _ (front _ (comm-↓↑ H CH)) ⟩
    CH • (CH ↑ • H ↓) • H ↓ • CH
      ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    CH • CH ↑ • (H ↓ • H ↓) • CH
      ≈⟨ back _ (back _ (cancelˢ _ H²)) ⟩
    CH • CH ↑ • CH ∎
    where open Tools ((₃₊ n) VRel,_===_)

  lhs146 rhs146 : Circuit (₃₊ n)
  lhs146 = U °CH • U °CZ° • °CH ↓ • U °CH • °CH ↓
  rhs146 = °CH ↓ • U °CH • °CH ↓ • U °CZ° • U °CH

  lhs146-form : (₃₊ n) ⊢ lhs146 ≈ N₂.⟪ Z ↑ ↑ • T ⟫
  lhs146-form {n} = begin
    U °CH • U °CZ° • °CH ↓ • U °CH • °CH ↓
      ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □) • (□ • □ • □)) Eq.refl ⟩
    (U °CH • U °CZ°) • (°CH ↓ • U °CH • °CH ↓)
      ≈⟨ cong (U-sem (°CH • °CZ°) (X ↑ • (Z ↑ • CH • CZ) • X ↑) Eq.refl)
              (sym (N₂.⟪⟫-•₃ (N₂-L °CH) refl (N₂-L °CH))) ⟩
    N₂.⟪ Z ↑ ↑ • CH ↑ • CZ ↑ ⟫ • N₂.⟪ °CH ↓ • CH ↑ • °CH ↓ ⟫
      ≈⟨ back _ (N₂.⟪⟫-cong °a-t-°a) ⟩
    N₂.⟪ Z ↑ ↑ • CH ↑ • CZ ↑ ⟫ • N₂.⟪ CH ↓ • CH ↑ • CH ↓ ⟫
      ≈⟨ sym (N₂.⟪⟫-• (Z ↑ ↑ • CH ↑ • CZ ↑) (CH ↓ • CH ↑ • CH ↓)) ⟩
    N₂.⟪ (Z ↑ ↑ • CH ↑ • CZ ↑) • (CH ↓ • CH ↑ • CH ↓) ⟫
      ≈⟨ N₂.⟪⟫-cong (by-assoc Eq.refl) ⟩
    N₂.⟪ Z ↑ ↑ • T ⟫ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  lhs146² : (₃₊ n) ⊢ lhs146 • lhs146 ≈ ε
  lhs146² {n} = begin
    lhs146 • lhs146
      ≈⟨ cong lhs146-form lhs146-form ⟩
    N₂.⟪ Z ↑ ↑ • T ⟫ • N₂.⟪ Z ↑ ↑ • T ⟫
      ≈⟨ N₂.⟪⟫-invol (invol-comm Z↑↑² T² ζ-T) ⟩
    ε ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)

  lhs146-rhs146 : (₃₊ n) ⊢ lhs146 • rhs146 ≈ ε
  lhs146-rhs146 {n} = begin
    lhs146 • rhs146
      ≈⟨ by-assoc Eq.refl ⟩
    ((((U °CH • U °CZ°) • °CH ↓) • U °CH) • °CH ↓) • (°CH ↓ • (U °CH • (°CH ↓ • (U °CZ° • U °CH))))
      ≈⟨ unwrap B² (unwrap A² (unwrap B² (unwrap D² A²))) ⟩
    ε ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    open Alg ((₃₊ n) VRel,_===_)
    A² : (₃₊ n) ⊢ U °CH • U °CH ≈ ε
    A² = U-sem (°CH • °CH) ε Eq.refl
    D² : (₃₊ n) ⊢ U °CZ° • U °CZ° ≈ ε
    D² = U-sem (°CZ° • °CZ°) ε Eq.refl
    B² : (₃₊ n) ⊢ °CH ↓ • °CH ↓ ≈ ε
    B² = L-sem (°CH • °CH) ε Eq.refl

-- (146)
eq146 : (₃₊ n) ⊢ U °CH • U °CZ° • °CH ↓ • U °CH • °CH ↓ ≈ °CH ↓ • U °CH • °CH ↓ • U °CZ° • U °CH
eq146 {n} = sym (inv-unique lhs146-rhs146 lhs146² refl)
  where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (147): again a word of involutions equal to its reverse

-- Write A, S, D′, D for the blocks °CH, HC, °CZ, °CZ° on the upper pair,
-- p and a for the outer and the lower CH, h for H on wire 0.  The word is
-- N₁ h with N₁ = A Y (a A a) and Y = S (D′ p) S, where (146) says that
-- M′ = A D (a A a) is an involution.  Now Y = D c with c = D Y, and N₁
-- is an involution as soon as c passes (a A a) A — `twist`.  Up to a
-- sign on wire 2, c is S p S conjugated by ρ = X H X on wire 0, which
-- turns H there into −H; so the claim is that S p S passes
-- Zᶻ = (aᶻ A aᶻ) A with aᶻ = a Z on wire 1.  The pieces of S p S are p, the
-- upper CZ and k, the lower P ⊗ P-conjugate of CZ carried to the outer
-- pair — (14) again, through P ⊗ P — and k passes Zᶻ because, through
-- P ⊗ P and the lower swap, that is the upper HC passing a doubly
-- controlled ZX with a white control on its wire: (17), as in (139).
module _ {n : ℕ} where
  open Tools ((₃₊ n) VRel,_===_)
  open Alg ((₃₊ n) VRel,_===_)

  private
    °t s °d °°d p a °a h t b : Circuit (₃₊ n)
    °t  = U °CH
    s   = U HC
    °d  = U °CZ
    °°d = U °CZ°
    p   = CH₂₀
    a   = CH ↓
    °a  = °CH ↓
    h   = H ↓
    t   = CH ↑
    b   = CZ₂₀

    -- Involutions.
    °t² : °t • °t ≈ ε
    °t² = U-sem (°CH • °CH) ε Eq.refl

    s² : s • s ≈ ε
    s² = U-sem (HC • HC) ε Eq.refl

    °d² : °d • °d ≈ ε
    °d² = U-sem (°CZ • °CZ) ε Eq.refl

    °°d² : °°d • °°d ≈ ε
    °°d² = U-sem (°CZ° • °CZ°) ε Eq.refl

    °a² : °a • °a ≈ ε
    °a² = L-sem (°CH • °CH) ε Eq.refl

    PP↑² : PP ↑ • PP ↑ ≈ ε
    PP↑² = U-sem (PP • PP) ε Eq.refl

    -- The upper HC and the lower CH share their control.
    s-a : s • a ≈ a • s
    s-a = S↑.⟪⟫-≈ eq133 (S↑.⟪⟫-•₂ refl S↑-CH₂₀) (S↑.⟪⟫-•₂ S↑-CH₂₀ refl)

    -- H on wire 0 passes everything in sight.
    h-U : (u : Circuit 2) → h • U u ≈ U u • h
    h-U u = U-comm H u

    h-p : h • p ≈ p • h
    h-p = begin
      h • p             ≈⟨ front _ (sym O-H↓) ⟩
      O (H ↓) • O CH    ≈⟨ sym (O-• (H ↓) CH) ⟩
      O (H ↓ • CH)      ≈⟨ O-sem (H ↓ • CH) (CH • H ↓) Eq.refl ⟩
      O (CH • H ↓)      ≈⟨ O-• CH (H ↓) ⟩
      O CH • O (H ↓)    ≈⟨ back _ O-H↓ ⟩
      p • h ∎

    h-a : h • a ≈ a • h
    h-a = L-sem (H ↓ • CH) (CH • H ↓) Eq.refl

    °a-form : °a ≈ a • h
    °a-form = L-sem °CH (CH • H ↓) Eq.refl

    °a-form′ : °a ≈ h • a
    °a-form′ = L-sem °CH (H ↓ • CH) Eq.refl

    ------------------------------------------------------------------
    -- The shape of the word

    Y N₁ M′ c Zw lhs147 rhs147 : Circuit (₃₊ n)
    Y      = s • (°d • p) • s
    N₁     = °t • Y • (a • °t • a)
    M′     = °t • °°d • (a • °t • a)
    c      = °°d • Y
    Zw     = (a • °t • a) • °t
    lhs147 = °t • s • °d • p • a • s • °t • °a
    rhs147 = °a • °t • s • a • p • °d • s • °t

    °d-p : °d • p ≈ p • °d
    °d-p = N₂.⟪⟫-≈ eq132 (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ CH₂₀)) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CH₂₀) refl)

    Y² : Y • Y ≈ ε
    Y² = conj-invol s² (invol-comm °d² CH₂₀² °d-p)

    lhs147-form : lhs147 ≈ N₁ • h
    lhs147-form = begin
      °t • s • °d • p • a • s • °t • °a
        ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
      °t • s • °d • p • (a • s) • °t • °a
        ≈⟨ back _ (back _ (back _ (back _ (cong (sym s-a) (back _ °a-form))))) ⟩
      °t • s • °d • p • (s • a) • °t • (a • h)
        ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □) • □ • (□ • □))
                     ((□ • (□ • (□ • □) • □) • (□ • □ • □)) • □) Eq.refl ⟩
      (°t • (s • (°d • p) • s) • (a • °t • a)) • h ∎

    h-N₁ : h • N₁ ≈ N₁ • h
    h-N₁ = comm-• (h-U °CH) (comm-• h-Y h-B)
      where
      h-Y : h • Y ≈ Y • h
      h-Y = comm-• (h-U HC) (comm-• (comm-• (h-U °CZ) h-p) (h-U HC))
      h-B : h • (a • °t • a) ≈ (a • °t • a) • h
      h-B = comm-• h-a (comm-• (h-U °CH) h-a)

    -- (146), with the negated lower CH replaced by the plain one.
    °a-°t-°a : °a • °t • °a ≈ a • °t • a
    °a-°t-°a = begin
      °a • °t • °a
        ≈⟨ cong °a-form (back _ °a-form′) ⟩
      (a • h) • °t • (h • a)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      a • (h • °t • h) • a
        ≈⟨ back _ (front _ (bzb H² (sym (h-U °CH)))) ⟩
      a • °t • a ∎

    M′² : M′ • M′ ≈ ε
    M′² = begin
      M′ • M′            ≈⟨ cong e e ⟩
      lhs146 • lhs146    ≈⟨ lhs146² ⟩
      ε ∎
      where
      e : M′ ≈ lhs146
      e = back _ (back _ (sym °a-°t-°a))

    ------------------------------------------------------------------
    -- c is S p S conjugated by ρ, up to the sign m

    ρ m aᶻ Zᶻ : Circuit (₃₊ n)
    ρ = X ↓ • H ↓ • X ↓
    m = U ((X • Z • X • Z) ↑)
    aᶻ = a • Z ↑
    Zᶻ = (aᶻ • °t • aᶻ) • °t

    ρ² : ρ • ρ ≈ ε
    ρ² = L-sem ((X ↓ • H ↓ • X ↓) • (X ↓ • H ↓ • X ↓)) ε Eq.refl

  private module R = Conj {₃₊ n} ρ ρ²

  private
    R-U : (u : Circuit 2) → R.⟪ U u ⟫ ≈ U u
    R-U u = R.⟪⟫-fix (U-comm (X • H • X) u)

    O-•₃ : (u v w : Circuit 2) → O (u • v • w) ≈ O u • O v • O w
    O-•₃ u v w = trans (O-• u (v • w)) (back _ (O-• v w))

    R-p : R.⟪ p ⟫ ≈ Z ↑ ↑ • p
    R-p = begin
      ρ • p • ρ
        ≈⟨ cong (sym O-ρ) (back _ (sym O-ρ)) ⟩
      O ρ₂ • O CH • O ρ₂
        ≈⟨ sym (O-•₃ ρ₂ CH ρ₂) ⟩
      O (ρ₂ • CH • ρ₂)
        ≈⟨ O-sem (ρ₂ • CH • ρ₂) (Z ↑ • CH) Eq.refl ⟩
      O (Z ↑ • CH)
        ≈⟨ O-• (Z ↑) CH ⟩
      O (Z ↑) • O CH
        ≈⟨ front _ (O-top Z) ⟩
      Z ↑ ↑ • p ∎
      where
      ρ₂ : Circuit 2
      ρ₂ = X ↓ • H ↓ • X ↓
      O-ρ : O ρ₂ ≈ ρ
      O-ρ = trans (O-•₃ (X ↓) (H ↓) (X ↓)) (cong O-X↓ (cong O-H↓ O-X↓))

    R-a : R.⟪ a ⟫ ≈ aᶻ
    R-a = L-sem ((X ↓ • H ↓ • X ↓) • CH • (X ↓ • H ↓ • X ↓)) (CH • Z ↑) Eq.refl

    c-form : c ≈ m • R.⟪ s • p • s ⟫
    c-form = begin
      °°d • s • (°d • p) • s
        ≈⟨ by-passoc (□ • □ • (□ • □) • □) ((□ • □ • □) • □ • □) Eq.refl ⟩
      (°°d • s • °d) • p • s
        ≈⟨ front _ (U-sem (°CZ° • HC • °CZ) ((X • Z • X • Z) ↑ • HC • Z ↑) Eq.refl) ⟩
      (m • s • Z ↑ ↑) • p • s
        ≈⟨ by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      m • s • (Z ↑ ↑ • p) • s
        ≈⟨ back _ (sym (R.⟪⟫-•₃ (R-U HC) R-p (R-U HC))) ⟩
      m • R.⟪ s • p • s ⟫ ∎

    m-Zw : m • Zw ≈ Zw • m
    m-Zw = comm-• (comm-• m-a (comm-• m-°t m-a)) m-°t
      where
      m-a : m • a ≈ a • m
      m-a = sym (L-comm CH (X • Z • X • Z))
      m-°t : m • °t ≈ °t • m
      m-°t = U-sem ((X • Z • X • Z) ↑ • °CH) (°CH • (X • Z • X • Z) ↑) Eq.refl

    ------------------------------------------------------------------
    -- S p S in pieces

    κ k : Circuit (₃₊ n)
    κ = PP↓.⟪ CZ ↓ ⟫
    k = S↑.⟪ κ ⟫

    -- (14) through P ⊗ P: the two CH gates in a row.
    Ξ-form : a • t • a • t ≈ CZ ↑ • κ • CZ ↑ • κ
    Ξ-form = begin
      a • t • a • t
        ≈⟨ sym (conj-sym PP² e) ⟩
      PP↓.⟪ t • CZ ↓ • t • CZ ↓ ⟫
        ≈⟨ PP↓.⟪⟫-•₄ PP-CH↑ refl PP-CH↑ refl ⟩
      CZ ↑ • κ • CZ ↑ • κ ∎
      where
      e : PP↓.⟪ a • t • a • t ⟫ ≈ t • CZ ↓ • t • CZ ↓
      e = trans (PP↓.⟪⟫-•₄ PP-CH↓ PP-CH↑ PP-CH↓ PP-CH↑) symm-controls₁

    psps : p • s • p • s ≈ CZ ↑ • k • CZ ↑ • k
    psps = S↑.⟪⟫-≈ Ξ-form (S↑.⟪⟫-•₄ S↑-CH↓ refl S↑-CH↓ refl)
                          (S↑.⟪⟫-•₄ S↑-CZ↑ refl S↑-CZ↑ refl)

    sps-form : s • p • s ≈ p • CZ ↑ • k • CZ ↑ • k
    sps-form = trans (insertˡ _ CH₂₀²) (back _ psps)

    ------------------------------------------------------------------
    -- k through P ⊗ P: the HC on the outer pair

    -- P ⊗ P on the outer pair, as the two P ⊗ P in either order.
    E-form : S↑.⟪ PP ↓ ⟫ ≈ PP ↓ • PP ↑
    E-form = sym eq130

    E-form′ : S↑.⟪ PP ↓ ⟫ ≈ PP ↑ • PP ↓
    E-form′ = sym (inv-unique (unwrap PP↑² PP²) (S↑.⟪⟫-invol PP²) eq130)

    -- A gate g between the two orders, under P ⊗ P below.
    peel : ∀ {g} → PP↓.⟪ (PP ↓ • PP ↑) • g • (PP ↑ • PP ↓) ⟫ ≈ PP ↑ • g • PP ↑
    peel {g} = begin
      PP ↓ • ((PP ↓ • PP ↑) • g • (PP ↑ • PP ↓)) • PP ↓
        ≈⟨ by-passoc (□ • ((□ • □) • □ • (□ • □)) • □) ((□ • □) • □ • □ • □ • (□ • □)) Eq.refl ⟩
      (PP ↓ • PP ↓) • PP ↑ • g • PP ↑ • (PP ↓ • PP ↓)
        ≈⟨ cancelˢ _ PP² ⟩
      PP ↑ • g • PP ↑ • (PP ↓ • PP ↓)
        ≈⟨ back _ (back _ (cancelᵉ _ PP²)) ⟩
      PP ↑ • g • PP ↑ ∎

    k-form : k ≈ (PP ↓ • PP ↑) • b • (PP ↑ • PP ↓)
    k-form = S↑.⟪⟫-•₃ E-form S↑-CZ↓ E-form′

    s-form : s ≈ (PP ↓ • PP ↑) • CZ ↑ • (PP ↑ • PP ↓)
    s-form = begin
      S↑.⟪ CH ↑ ⟫                  ≈⟨ S↑.⟪⟫-cong (sym PP-CZ↑) ⟩
      S↑.⟪ PP↓.⟪ CZ ↑ ⟫ ⟫          ≈⟨ S↑.⟪⟫-•₃ E-form S↑-CZ↑ E-form′ ⟩
      (PP ↓ • PP ↑) • CZ ↑ • (PP ↑ • PP ↓) ∎

    OHC-form : O HC ≈ PP ↑ • b • PP ↑
    OHC-form = begin
      S↓.⟪ s ⟫
        ≈⟨ S↓.⟪⟫-cong s-form ⟩
      S↓.⟪ (PP ↓ • PP ↑) • CZ ↑ • (PP ↑ • PP ↓) ⟫
        ≈⟨ S↓.⟪⟫-•₃ (S↓.⟪⟫-•₂ S-PP↓ S-PP↑) refl (S↓.⟪⟫-•₂ S-PP↑′ S-PP↓) ⟩
      (PP ↓ • (PP ↓ • PP ↑)) • b • ((PP ↑ • PP ↓) • PP ↓)
        ≈⟨ by-passoc ((□ • (□ • □)) • □ • ((□ • □) • □)) ((□ • □) • □ • □ • □ • (□ • □)) Eq.refl ⟩
      (PP ↓ • PP ↓) • PP ↑ • b • PP ↑ • (PP ↓ • PP ↓)
        ≈⟨ cancelˢ _ PP² ⟩
      PP ↑ • b • PP ↑ • (PP ↓ • PP ↓)
        ≈⟨ back _ (back _ (cancelᵉ _ PP²)) ⟩
      PP ↑ • b • PP ↑ ∎
      where
      S-PP↓ : S↓.⟪ PP ↓ ⟫ ≈ PP ↓
      S-PP↓ = L-sem (Ex • PP • Ex) PP Eq.refl
      S-PP↑ : S↓.⟪ PP ↑ ⟫ ≈ PP ↓ • PP ↑
      S-PP↑ = trans (sym (O-L PP)) E-form
      S-PP↑′ : S↓.⟪ PP ↑ ⟫ ≈ PP ↑ • PP ↓
      S-PP↑′ = trans (sym (O-L PP)) E-form′

    PP-k : PP↓.⟪ k ⟫ ≈ O HC
    PP-k = begin
      PP↓.⟪ k ⟫                                      ≈⟨ PP↓.⟪⟫-cong k-form ⟩
      PP↓.⟪ (PP ↓ • PP ↑) • b • (PP ↑ • PP ↓) ⟫      ≈⟨ peel ⟩
      PP ↑ • b • PP ↑                                ≈⟨ sym OHC-form ⟩
      O HC ∎

    ------------------------------------------------------------------
    -- Zᶻ through P ⊗ P and the lower swap: a doubly controlled ZX

    °b z V° Φ Ωᶻ : Circuit (₃₊ n)
    °b = °CZ₂₀
    z  = Z ↓
    V° = N₁.⟪ CCXZ ⟫
    Φ  = (°a • °b • °a) • °b
    Ωᶻ  = ((HC ↓ • H ↑) • °d • (HC ↓ • H ↑)) • °d

    PP-Zᶻ : PP↓.⟪ Zᶻ ⟫ ≈ Ωᶻ
    PP-Zᶻ = PP↓.⟪⟫-•₂ (PP↓.⟪⟫-•₃ e₁ e₂ e₁) e₂
      where
      e₁ : PP↓.⟪ aᶻ ⟫ ≈ HC ↓ • H ↑
      e₁ = PP↓.⟪⟫-•₂ PP-CH↓ PP-Z↑
      e₂ : PP↓.⟪ °t ⟫ ≈ °d
      e₂ = PP↓.⟪⟫-•₃ (PP-top X) PP-CH↑ (PP-top X)

    S-Φ : S↓.⟪ Φ ⟫ ≈ Ωᶻ
    S-Φ = S↓.⟪⟫-•₂ (S↓.⟪⟫-•₃ e₁ e₂ e₁) e₂
      where
      e₁ : S↓.⟪ °a ⟫ ≈ HC ↓ • H ↑
      e₁ = L-sem (Ex • °CH • Ex) (HC • H ↑) Eq.refl
      e₂ : S↓.⟪ °b ⟫ ≈ °d
      e₂ = trans (S↓.⟪⟫-cong °CZ₂₀-O) (S↓.⟪⟫-⟪⟫ (U °CZ))

    -- Φ is the doubly controlled ZX with both controls white, written
    -- with the controlled ZX on the lower pair.
    Φ-form : Φ ≈ (°a • z • °a • z) • V°
    Φ-form = begin
      (°a • °b • °a) • °b
        ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
      °a • °b • °a • °b
        ≈⟨ sym (N₁.⟪⟫-•₄ refl N₁-°b refl N₁-°b) ⟩
      N₁.⟪ CH • °b • CH • °b ⟫
        ≈⟨ N₁.⟪⟫-cong (trans (sym °CCZX-form′) split) ⟩
      N₁.⟪ L (ΛZX 1) • CCXZ ⟫
        ≈⟨ N₁.⟪⟫-•₂ (trans (N₁.⟪⟫-cong CZX↓) (N₁.⟪⟫-•₄ refl N₁-z refl N₁-z)) refl ⟩
      (°a • z • °a • z) • V° ∎
      where
      N₁-°b : N₁.⟪ °b ⟫ ≈ °b
      N₁-°b = N₁.⟪⟫-fix (trans (back _ °CZ₂₀-O) (trans (X↑-O °CZ) (front _ (sym °CZ₂₀-O))))
      N₁-z : N₁.⟪ z ⟫ ≈ z
      N₁-z = N₁.⟪⟫-fix (sym (comm-↓↑ Z X))
      split : °CCZX ≈ L (ΛZX 1) • CCXZ
      split = begin
        °CCZX                     ≈⟨ sym right-unit ⟩
        °CCZX • ε                 ≈⟨ back _ (sym eq117) ⟩
        °CCZX • (CCZX • CCXZ)     ≈⟨ sym assoc ⟩
        (°CCZX • CCZX) • CCXZ     ≈⟨ front _ eq136 ⟩
        L (ΛZX 1) • CCXZ ∎

    -- The upper HC passes it: (17), in the form CH↑-°CCXZ, through the
    -- upper swap.
    s-V° : s • V° ≈ V° • s
    s-V° = S↑.⟪⟫-≈ CH↑-°CCXZ (S↑.⟪⟫-•₂ refl S-°V) (S↑.⟪⟫-•₂ S-°V refl)
      where
      S-W : S↑.⟪ CCZX ⟫ ≈ CCZX
      S-W = S↑.⟪⟫-fix (sym eq127)
      S-V : S↑.⟪ CCXZ ⟫ ≈ CCXZ
      S-V = begin
        S↑.⟪ CCXZ ⟫          ≈⟨ S↑.⟪⟫-cong (sym eq124) ⟩
        S↑.⟪ CCZX • CZ ↑ ⟫   ≈⟨ S↑.⟪⟫-•₂ S-W S↑-CZ↑ ⟩
        CCZX • CZ ↑          ≈⟨ eq124 ⟩
        CCXZ ∎
      S-X₂ : S↑.⟪ X ↑ ↑ ⟫ ≈ X ↑
      S-X₂ = U-sem (Ex • X ↑ • Ex) (X ↓) Eq.refl
      S-°V : S↑.⟪ °CCXZ ⟫ ≈ V°
      S-°V = S↑.⟪⟫-•₃ S-X₂ S-V S-X₂

    s-Φ : s • Φ ≈ Φ • s
    s-Φ = begin
      s • Φ                          ≈⟨ back _ Φ-form ⟩
      s • ((°a • z • °a • z) • V°)   ≈⟨ comm-• (comm-abab s-°a s-z) s-V° ⟩
      ((°a • z • °a • z) • V°) • s   ≈⟨ front _ (sym Φ-form) ⟩
      Φ • s ∎
      where
      s-°a : s • °a ≈ °a • s
      s-°a = begin
        s • °a         ≈⟨ back _ °a-form ⟩
        s • (a • h)    ≈⟨ comm-• s-a (sym (h-U HC)) ⟩
        (a • h) • s    ≈⟨ front _ (sym °a-form) ⟩
        °a • s ∎
      s-z : s • z ≈ z • s
      s-z = sym (U-comm Z HC)

    k-Zᶻ : k • Zᶻ ≈ Zᶻ • k
    k-Zᶻ = PP↓.⟪⟫-≈ OHC-Ωᶻ (PP↓.⟪⟫-•₂ PP-OHC PP-Ωᶻ) (PP↓.⟪⟫-•₂ PP-Ωᶻ PP-OHC)
      where
      OHC-Ωᶻ : O HC • Ωᶻ ≈ Ωᶻ • O HC
      OHC-Ωᶻ = S↓.⟪⟫-≈ s-Φ (S↓.⟪⟫-•₂ refl S-Φ) (S↓.⟪⟫-•₂ S-Φ refl)
      PP-OHC : PP↓.⟪ O HC ⟫ ≈ k
      PP-OHC = conj-sym PP² PP-k
      PP-Ωᶻ : PP↓.⟪ Ωᶻ ⟫ ≈ Zᶻ
      PP-Ωᶻ = conj-sym PP² PP-Zᶻ

    ------------------------------------------------------------------
    -- Assembly

    sps-Zᶻ : (s • p • s) • Zᶻ ≈ Zᶻ • (s • p • s)
    sps-Zᶻ = begin
      (s • p • s) • Zᶻ
        ≈⟨ front _ sps-form ⟩
      (p • CZ ↑ • k • CZ ↑ • k) • Zᶻ
        ≈⟨ sym (comm-• (sym p-Zᶻ) (comm-• (sym cz-Zᶻ) (comm-• (sym k-Zᶻ) (comm-• (sym cz-Zᶻ) (sym k-Zᶻ))))) ⟩
      Zᶻ • (p • CZ ↑ • k • CZ ↑ • k)
        ≈⟨ back _ (sym sps-form) ⟩
      Zᶻ • (s • p • s) ∎
      where
      p-°t : p • °t ≈ °t • p
      p-°t = sym (N₂.⟪⟫-≈ eq134 (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ CH₂₀)) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CH₂₀) refl))
      p-aᶻ : p • aᶻ ≈ aᶻ • p
      p-aᶻ = comm-• eq135 (sym (Z↑-O CH))
      p-Zᶻ : p • Zᶻ ≈ Zᶻ • p
      p-Zᶻ = comm-• (comm-• p-aᶻ (comm-• p-°t p-aᶻ)) p-°t
      cz-°t : CZ ↑ • °t ≈ °t • CZ ↑
      cz-°t = U-sem (CZ • °CH) (°CH • CZ) Eq.refl
      cz-aᶻ : CZ ↑ • aᶻ ≈ aᶻ • CZ ↑
      cz-aᶻ = comm-• (ax comm-CZ↑-CH↓) (U-sem (CZ • Z ↓) (Z ↓ • CZ) Eq.refl)
      cz-Zᶻ : CZ ↑ • Zᶻ ≈ Zᶻ • CZ ↑
      cz-Zᶻ = comm-• (comm-• cz-aᶻ (comm-• cz-°t cz-aᶻ)) cz-°t

    c-Zw : c • Zw ≈ Zw • c
    c-Zw = begin
      c • Zw                        ≈⟨ front _ c-form ⟩
      (m • R.⟪ s • p • s ⟫) • Zw    ≈⟨ pass-xy R-sps m-Zw ⟩
      Zw • (m • R.⟪ s • p • s ⟫)    ≈⟨ back _ (sym c-form) ⟩
      Zw • c ∎
      where
      R-aᶻ : R.⟪ aᶻ ⟫ ≈ a
      R-aᶻ = conj-sym ρ² R-a
      R-Zᶻ : R.⟪ Zᶻ ⟫ ≈ Zw
      R-Zᶻ = R.⟪⟫-•₂ (R.⟪⟫-•₃ R-aᶻ (R-U °CH) R-aᶻ) (R-U °CH)
      R-sps : R.⟪ s • p • s ⟫ • Zw ≈ Zw • R.⟪ s • p • s ⟫
      R-sps = R.⟪⟫-≈ sps-Zᶻ (R.⟪⟫-•₂ refl R-Zᶻ) (R.⟪⟫-•₂ R-Zᶻ refl)

    N₁² : N₁ • N₁ ≈ ε
    N₁² = begin
      N₁ • N₁
        ≈⟨ cong e e ⟩
      (°t • (°°d • c) • (a • °t • a)) • (°t • (°°d • c) • (a • °t • a))
        ≈⟨ twist c-Zw cdc M′² ⟩
      ε ∎
      where
      e : N₁ ≈ °t • (°°d • c) • (a • °t • a)
      e = back _ (front _ (insertˡ _ °°d²))
      cdc : c • °°d • c ≈ °°d
      cdc = begin
        (°°d • Y) • °°d • (°°d • Y)
          ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • □ • (□ • □) • □) Eq.refl ⟩
        °°d • Y • (°°d • °°d) • Y
          ≈⟨ back _ (back _ (cancelˢ _ °°d²)) ⟩
        °°d • Y • Y
          ≈⟨ back _ Y² ⟩
        °°d • ε
          ≈⟨ right-unit ⟩
        °°d ∎

    lhs147² : lhs147 • lhs147 ≈ ε
    lhs147² = begin
      lhs147 • lhs147        ≈⟨ cong lhs147-form lhs147-form ⟩
      (N₁ • h) • (N₁ • h)    ≈⟨ invol-comm N₁² H² (sym h-N₁) ⟩
      ε ∎

    lhs147-rhs147 : lhs147 • rhs147 ≈ ε
    lhs147-rhs147 = begin
      lhs147 • rhs147
        ≈⟨ by-passoc ((□ • □ • □ • □ • □ • □ • □ • □) • (□ • □ • □ • □ • □ • □ • □ • □))
                     ((((((((□ • □) • □) • □) • □) • □) • □) • □) • (□ • □ • □ • □ • □ • □ • □ • □)) Eq.refl ⟩
      (((((((°t • s) • °d) • p) • a) • s) • °t) • °a) • (°a • °t • s • a • p • °d • s • °t)
        ≈⟨ unwrap °a² (unwrap °t² (unwrap s² (unwrap CH² (unwrap CH₂₀² (unwrap °d² (unwrap s² °t²)))))) ⟩
      ε ∎

  -- (147)
  eq147 : (₃₊ n) ⊢ U °CH • U HC • U °CZ • CH₂₀ • CH ↓ • U HC • U °CH • °CH ↓
                 ≈ °CH ↓ • U °CH • U HC • CH ↓ • CH₂₀ • U °CZ • U HC • U °CH
  eq147 = sym (inv-unique lhs147-rhs147 lhs147² refl)

------------------------------------------------------------------------
-- For the four-qubit stage: Z and H on the target exchange CCZX and CCXZ

Z↓-CCZX : (₃₊ n) ⊢ Z ↓ • CCZX ≈ CCXZ • Z ↓
Z↓-CCZX = z-W

H↓-CCXZ : (₃₊ n) ⊢ H ↓ • CCXZ ≈ CCZX • H ↓
H↓-CCXZ = h-V

CH↓-CCZX : (₃₊ n) ⊢ CH ↓ • CCZX ≈ CCXZ • CH ↓
CH↓-CCZX = a-W

CH↓-CCXZ : (₃₊ n) ⊢ CH ↓ • CCXZ ≈ CCZX • CH ↓
CH↓-CCXZ = a-V

H↓-CCZX : (₃₊ n) ⊢ H ↓ • CCZX ≈ CCXZ • H ↓
H↓-CCZX {n} = begin
  H ↓ • CCZX                  ≈⟨ back _ (insertʳ _ H²) ⟩
  H ↓ • (CCZX • H ↓) • H ↓    ≈⟨ back _ (front _ (sym h-V)) ⟩
  H ↓ • (H ↓ • CCXZ) • H ↓    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (H ↓ • H ↓) • CCXZ • H ↓    ≈⟨ cancelˢ _ H² ⟩
  CCXZ • H ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)
