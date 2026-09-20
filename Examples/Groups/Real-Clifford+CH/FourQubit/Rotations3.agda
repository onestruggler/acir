------------------------------------------------------------------------
-- Presentations of groups
--
-- The triply controlled ZX and XZ (Clément, Lemma D.5, Equations
-- (208)–(215))
--
-- Definition 2.4 makes the triply controlled ZX on wire 0 of the CH from
-- wire 1 and the box on wire 1, a B a B, and XZ of the same two letters
-- in the other order: two words of involutions, inverse to each other,
-- (208), (209).  The CH is the product of the doubly controlled H of the
-- two colours, (171), and the white one passes the box, (181), and the
-- black one: so a may be replaced by the doubly controlled H, (210),
-- (211).  And the box on wire 1 is the CZ of wires 0 and 3 times its
-- white version, (170), which the H gate passes as well: so B may then be
-- replaced by that CZ, (212), (213).  Each form is fixed by one of the
-- swaps of two controls, (214), (215).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; CH²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀² ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq167 ; eq170 ; eq170′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (eq181ᵇ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (S₁₂-P₀₃ ; S₁₂-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (S₂₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (eq171ᶜ ; ΛH₂′-°ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The triply controlled ZX and XZ on wire 0, from wires 1, 2, 3.
ZX₃ XZ₃ : Circuit (₄₊ n)
ZX₃ {n} = ΛZX 3 ↓ᵏ n
XZ₃ {n} = ΛXZ 3 ↓ᵏ n

-- The doubly controlled H is an involution, in any position.
ΛH₂′² : (₄₊ n) ⊢ ΛH₂′ • ΛH₂′ ≈ ε
ΛH₂′² = S₂₃.⟪⟫-invol (S₁₂.⟪⟫-invol (S₀₁.⟪⟫-invol eq167))

°ΛH₂′² : (₄₊ n) ⊢ °ΛH₂′ • °ΛH₂′ ≈ ε
°ΛH₂′² = N₂.⟪⟫-invol ΛH₂′²

box₃′² : (₄₊ n) ⊢ box₃′ • box₃′ ≈ ε
box₃′² = S₀₁.⟪⟫-invol eq166

------------------------------------------------------------------------
-- (208), (209)

module _ {n : ℕ} where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

  private
    a B °B G °G c : Circuit (₄₊ n)
    a  = CH ↓
    B  = box₃′
    °B = S₀₁.⟪ °box₃ ⟫
    G  = ΛH₂′
    °G = °ΛH₂′
    c  = CZ₃₀

  -- (208)
  eq208 : XZ₃ • ZX₃ ≈ ε
  eq208 = invol-abab box₃′² CH²

  eq208′ : ZX₃ • XZ₃ ≈ ε
  eq208′ = invol-abab CH² box₃′²

  -- (209): on wire 1, from wires 0, 3 and, negatively, 2.
  eq209 : S₀₁.⟪ N₂.⟪ XZ₃ ⟫ ⟫ • S₀₁.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ≈ ε
  eq209 = begin
    S₀₁.⟪ N₂.⟪ XZ₃ ⟫ ⟫ • S₀₁.⟪ N₂.⟪ ZX₃ ⟫ ⟫   ≈⟨ sym (S₀₁.⟪⟫-• (N₂.⟪ XZ₃ ⟫) (N₂.⟪ ZX₃ ⟫)) ⟩
    S₀₁.⟪ N₂.⟪ XZ₃ ⟫ • N₂.⟪ ZX₃ ⟫ ⟫           ≈⟨ S₀₁.⟪⟫-cong (sym (N₂.⟪⟫-• XZ₃ ZX₃)) ⟩
    S₀₁.⟪ N₂.⟪ XZ₃ • ZX₃ ⟫ ⟫                  ≈⟨ S₀₁.⟪⟫-cong (N₂.⟪⟫-cong eq208) ⟩
    S₀₁.⟪ N₂.⟪ ε ⟫ ⟫                          ≈⟨ S₀₁.⟪⟫-cong N₂.⟪⟫-ε ⟩
    S₀₁.⟪ ε ⟫                                 ≈⟨ S₀₁.⟪⟫-ε ⟩
    ε ∎

  ----------------------------------------------------------------------
  -- (210), (211): the doubly controlled H for the CH

  -- The CH with the white H gate taken off is the black one.
  private
    a-form : a ≈ G • °G
    a-form = sym eq171ᶜ

  -- (210)
  eq210 : ZX₃ ≈ G • B • G • B
  eq210 = begin
    a • B • a • B
      ≈⟨ cong a-form (back _ (front _ a-form)) ⟩
    (G • °G) • B • (G • °G) • B
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    G • (°G • B) • G • °G • B
      ≈⟨ back _ (front _ (sym eq181)) ⟩
    G • (B • °G) • G • °G • B
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    G • B • (°G • G) • °G • B
      ≈⟨ back _ (back _ (front _ (sym ΛH₂′-°ΛH₂′))) ⟩
    G • B • (G • °G) • °G • B
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    G • B • G • (°G • °G) • B
      ≈⟨ back _ (back _ (back _ (trans (front _ °ΛH₂′²) left-unit))) ⟩
    G • B • G • B ∎

  -- (211)
  eq211 : XZ₃ ≈ B • G • B • G
  eq211 = inv-unique eq208′ (invol-abab box₃′² ΛH₂′²) eq210

  ----------------------------------------------------------------------
  -- (212), (213): the CZ of wires 0 and 3 for the box

  private
    °B² : °B • °B ≈ ε
    °B² = S₀₁.⟪⟫-invol (N₂.⟪⟫-invol eq166)

    S-c : S₀₁.⟪ P₁₃ CZ ⟫ ≈ c
    S-c = sym CZ₃₀-P

    -- (170) under the lower swap, in both orders.
    B°B : B • °B ≈ c
    B°B = S₀₁.⟪⟫-≈ eq170 (S₀₁.⟪⟫-• box₃ °box₃) S-c

    °BB : °B • B ≈ c
    °BB = S₀₁.⟪⟫-≈ eq170′ (S₀₁.⟪⟫-• °box₃ box₃) S-c

    B-form : B ≈ c • °B
    B-form = begin
      B               ≈⟨ sym right-unit ⟩
      B • ε           ≈⟨ back _ (sym °B²) ⟩
      B • °B • °B     ≈⟨ sym assoc ⟩
      (B • °B) • °B   ≈⟨ front _ B°B ⟩
      c • °B ∎

    B-form′ : B ≈ °B • c
    B-form′ = begin
      B               ≈⟨ sym left-unit ⟩
      ε • B           ≈⟨ front _ (sym °B²) ⟩
      (°B • °B) • B   ≈⟨ assoc ⟩
      °B • °B • B     ≈⟨ back _ °BB ⟩
      °B • c ∎

  -- (212)
  eq212 : ZX₃ ≈ G • c • G • c
  eq212 = begin
    ZX₃
      ≈⟨ eq210 ⟩
    G • B • G • B
      ≈⟨ back _ (cong B-form (back _ B-form′)) ⟩
    G • (c • °B) • G • °B • c
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    G • c • (°B • G) • °B • c
      ≈⟨ back _ (back _ (front _ eq181ᵇ)) ⟩
    G • c • (G • °B) • °B • c
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    G • c • G • (°B • °B) • c
      ≈⟨ back _ (back _ (back _ (trans (front _ °B²) left-unit))) ⟩
    G • c • G • c ∎

  -- (213)
  eq213 : XZ₃ ≈ c • G • c • G
  eq213 = inv-unique eq208′ (invol-abab CZ₃₀² ΛH₂′²) eq212

  ----------------------------------------------------------------------
  -- (214), (215): symmetric in the controls

  -- The upper swap fixes both letters of the definition.
  S₂₃-ZX₃ : S₂₃.⟪ ZX₃ ⟫ ≈ ZX₃
  S₂₃-ZX₃ = S₂₃.⟪⟫-•₄ (L-S₂₃ CH) S₂₃-box₃′ (L-S₂₃ CH) S₂₃-box₃′

  S₂₃-XZ₃ : S₂₃.⟪ XZ₃ ⟫ ≈ XZ₃
  S₂₃-XZ₃ = S₂₃.⟪⟫-•₄ S₂₃-box₃′ (L-S₂₃ CH) S₂₃-box₃′ (L-S₂₃ CH)

  -- The middle swap fixes both letters of (212).
  private
    S₁₂-c : S₁₂.⟪ c ⟫ ≈ c
    S₁₂-c = trans (S₁₂.⟪⟫-cong CZ₃₀-P) (trans (S₁₂-P₀₃ CZ) (sym CZ₃₀-P))

  S₁₂-ZX₃ : S₁₂.⟪ ZX₃ ⟫ ≈ ZX₃
  S₁₂-ZX₃ = trans (S₁₂.⟪⟫-cong eq212)
           (trans (S₁₂.⟪⟫-•₄ S₁₂-ΛH₂′ S₁₂-c S₁₂-ΛH₂′ S₁₂-c) (sym eq212))

  S₁₂-XZ₃ : S₁₂.⟪ XZ₃ ⟫ ≈ XZ₃
  S₁₂-XZ₃ = trans (S₁₂.⟪⟫-cong eq213)
           (trans (S₁₂.⟪⟫-•₄ S₁₂-c S₁₂-ΛH₂′ S₁₂-c S₁₂-ΛH₂′) (sym eq213))

  -- (214)
  eq214 : ZX₃ • Ex ↑ ↑ ≈ Ex ↑ ↑ • ZX₃
  eq214 = sym (S₂₃.⟪⟫-comm S₂₃-ZX₃)

  eq214′ : XZ₃ • Ex ↑ ↑ ≈ Ex ↑ ↑ • XZ₃
  eq214′ = sym (S₂₃.⟪⟫-comm S₂₃-XZ₃)

  -- (215)
  eq215 : ZX₃ • Ex ↑ ≈ Ex ↑ • ZX₃
  eq215 = sym (S₁₂.⟪⟫-comm S₁₂-ZX₃)

  eq215′ : XZ₃ • Ex ↑ ≈ Ex ↑ • XZ₃
  eq215′ = sym (S₁₂.⟪⟫-comm S₁₂-XZ₃)
