------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled gates on four qubits (Clément, Lemma D.5, Equations (164)
-- and (167)–(171))
--
-- Gates that share only control wires with the box, or with the doubly
-- controlled ZX one wire up, pass them; and the doubly controlled H of
-- Definition 2.4 is an involution.  The box and its version with the
-- control on wire 2 negated merge into the CZ of wires 1 and 3, (170),
-- and the two doubly controlled H gates into the CH, (171).  In
-- progress: (172) onwards.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Controlled
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq124 ; eq137 ; eq141 ; CH↑-CZ₂₀ ; CZ₂₀² ; CZX↓ ; °CCZX ; °CCXZ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (164): the negated CH of wires 1 and 2 passes the box

-- Its control is wire 2, a control of the box, and negated; its target
-- wire 1, another.
eq164 : (₄₊ n) ⊢ U °CH • box₃ ≈ box₃ • U °CH
eq164 {n} = comm-• t-W (comm-• t-c (comm-• t-V t-c))
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  t-W : (₄₊ n) ⊢ U °CH • CCZX ≈ CCZX • U °CH
  t-W = L₃-comm (U₀ °CH) CCZX Eq.refl
  t-V : (₄₊ n) ⊢ U °CH • CCXZ ≈ CCXZ • U °CH
  t-V = comm-inv eq117 eq118 t-W
  t-c : (₄₊ n) ⊢ U °CH • CZ₃₀ ≈ CZ₃₀ • U °CH
  t-c = begin
    U °CH • CZ₃₀       ≈⟨ back _ CZ₃₀-P ⟩
    U °CH • P₀₃ CZ     ≈⟨ sym (P₀₃-U CZ °CH) ⟩
    P₀₃ CZ • U °CH     ≈⟨ front _ (sym CZ₃₀-P) ⟩
    CZ₃₀ • U °CH ∎

------------------------------------------------------------------------
-- (167): the doubly controlled H is an involution

eq167 : (₄₊ n) ⊢ (ΛH 2 ↓ᵏ n) • (ΛH 2 ↓ᵏ n) ≈ ε
eq167 {n} = conj-invol (L-sem (PP • PP) ε Eq.refl) eq166
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (168), (169): what passes the doubly controlled ZX one wire up

-- CCZX ↑ has its target on wire 1 and its controls on wires 2 and 3.  A
-- gate from one of its control wires to wire 0 passes it.
eq168 : (₄₊ n) ⊢ CZ₂₀ • CCZX ↑ ≈ CCZX ↑ • CZ₂₀
eq168 {n} = comm-abab (sym CH↑-CZ₂₀) (sym (P₁₃-O CZ CZ))
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

eq169 : (₄₊ n) ⊢ CH₃₀ • CCZX ↑ ≈ CCZX ↑ • CH₃₀
eq169 {n} = begin
  CH₃₀ • CCZX ↑       ≈⟨ front _ CH₃₀-P ⟩
  P₀₃ CH • CCZX ↑     ≈⟨ comm-abab (P₀₃-U CH CH) (sym (comm-13-03 CZ CH (evaluated Eq.refl))) ⟩
  CCZX ↑ • P₀₃ CH     ≈⟨ back _ (sym CH₃₀-P) ⟩
  CCZX ↑ • CH₃₀ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (170): a black and a white control merge

-- The box with its control on wire 2 negated.
°box₃ : Circuit (₄₊ n)
°box₃ = N₂.⟪ box₃ ⟫

private
  N₂-c : (₄₊ n) ⊢ N₂.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
  N₂-c {n} = begin
    N₂.⟪ CZ₃₀ ⟫       ≈⟨ N₂.⟪⟫-cong CZ₃₀-P ⟩
    N₂.⟪ P₀₃ CZ ⟫     ≈⟨ N₂.⟪⟫-fix (sym (P₀₃-U CZ (X ↑))) ⟩
    P₀₃ CZ            ≈⟨ sym CZ₃₀-P ⟩
    CZ₃₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  °box-form : (₄₊ n) ⊢ °box₃ ≈ CZ₃₀ • °CCZX • CZ₃₀ • °CCXZ
  °box-form {n} = trans (N₂.⟪⟫-cong eq165) (N₂.⟪⟫-•₄ N₂-c refl N₂-c refl)
    where open Tools ((₄₊ n) VRel,_===_)

  -- The CZ from wire 3 turns the controlled ZX from wire 1 into itself
  -- times the CZ of wires 1 and 3: on the triple 0 1 3.
  cCc : (₄₊ n) ⊢ CZ₃₀ • L (ΛZX 1) • CZ₃₀ ≈ L (ΛZX 1) • P₁₃ CZ
  cCc {n} = begin
    CZ₃₀ • L (ΛZX 1) • CZ₃₀
      ≈⟨ cong CZ₃₀-P (cong CZX↓ CZ₃₀-P) ⟩
    P₀₃ CZ • L g • P₀₃ CZ
      ≈⟨ sym (cong (M₃-O CZ) (cong (M₃-L g) (M₃-O CZ))) ⟩
    M₃ (O₀ CZ) • M₃ (L₀ g) • M₃ (O₀ CZ)
      ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
    M₃ (O₀ CZ • L₀ g • O₀ CZ)
      ≈⟨ M₃-sem (O₀ CZ • L₀ g • O₀ CZ) (L₀ g • U₀ CZ) Eq.refl ⟩
    M₃ (L₀ g • U₀ CZ)
      ≈⟨ S₂₃.⟪⟫-•₂ refl refl ⟩
    M₃ (L₀ g) • M₃ (U₀ CZ)
      ≈⟨ cong (M₃-L g) (M₃-U CZ) ⟩
    L g • P₁₃ CZ
      ≈⟨ front _ (sym CZX↓) ⟩
    L (ΛZX 1) • P₁₃ CZ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    g : Circuit 2
    g = CH • Z ↓ • CH • Z ↓

  -- The CZ of wires 1 and 3 passes the negated CCZX.
  d′-°W : (₄₊ n) ⊢ P₁₃ CZ • °CCZX ≈ °CCZX • P₁₃ CZ
  d′-°W {n} = comm-• d′-X (comm-• (comm-abab d′-a (P₁₃-O CZ CZ)) d′-X)
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    d′-X : (₄₊ n) ⊢ P₁₃ CZ • X ↑ ↑ ≈ X ↑ ↑ • P₁₃ CZ
    d′-X = sym (comm-12-13 (X ↑) CZ (evaluated Eq.refl))
    d′-a : (₄₊ n) ⊢ P₁₃ CZ • CH ↓ ≈ CH ↓ • P₁₃ CZ
    d′-a = sym (comm-01-13 CH CZ (evaluated Eq.refl))

  °W°V : (₄₊ n) ⊢ °CCZX • °CCXZ ≈ ε
  °W°V {n} = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

-- (170), first equality
eq170 : (₄₊ n) ⊢ box₃ • °box₃ ≈ P₁₃ CZ
eq170 {n} = begin
  box₃ • °box₃
    ≈⟨ back _ °box-form ⟩
  (CCZX • CZ₃₀ • CCXZ • CZ₃₀) • (CZ₃₀ • °CCZX • CZ₃₀ • °CCXZ)
    ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
  CCZX • CZ₃₀ • CCXZ • (CZ₃₀ • CZ₃₀) • °CCZX • CZ₃₀ • °CCXZ
    ≈⟨ back _ (back _ (back _ (cancelˢ _ CZ₃₀²))) ⟩
  CCZX • CZ₃₀ • CCXZ • °CCZX • CZ₃₀ • °CCXZ
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  CCZX • CZ₃₀ • (CCXZ • °CCZX) • CZ₃₀ • °CCXZ
    ≈⟨ back _ (back _ (front _ eq141)) ⟩
  CCZX • CZ₃₀ • (CZ ↑ • L (ΛZX 1)) • CZ₃₀ • °CCXZ
    ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
  CCZX • (CZ₃₀ • CZ ↑) • L (ΛZX 1) • CZ₃₀ • °CCXZ
    ≈⟨ back _ (front _ (sym CZ↑-CZ₃₀)) ⟩
  CCZX • (CZ ↑ • CZ₃₀) • L (ΛZX 1) • CZ₃₀ • °CCXZ
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □ • □) • □) Eq.refl ⟩
  (CCZX • CZ ↑) • (CZ₃₀ • L (ΛZX 1) • CZ₃₀) • °CCXZ
    ≈⟨ cong eq124 (front _ cCc) ⟩
  CCXZ • (L (ΛZX 1) • P₁₃ CZ) • °CCXZ
    ≈⟨ back _ (front _ (front _ (sym eq137))) ⟩
  CCXZ • ((CCZX • °CCZX) • P₁₃ CZ) • °CCXZ
    ≈⟨ by-passoc (□ • ((□ • □) • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (CCXZ • CCZX) • °CCZX • P₁₃ CZ • °CCXZ
    ≈⟨ trans (front _ eq118) left-unit ⟩
  °CCZX • P₁₃ CZ • °CCXZ
    ≈⟨ trans (sym assoc) (front _ (sym d′-°W)) ⟩
  (P₁₃ CZ • °CCZX) • °CCXZ
    ≈⟨ assoc ⟩
  P₁₃ CZ • °CCZX • °CCXZ
    ≈⟨ back _ °W°V ⟩
  P₁₃ CZ • ε
    ≈⟨ right-unit ⟩
  P₁₃ CZ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- (170), second equality: the other order, by inverses.
eq170′ : (₄₊ n) ⊢ °box₃ • box₃ ≈ P₁₃ CZ
eq170′ {n} = inv-unique (unwrap′ (N₂.⟪⟫-invol eq166) eq166) d′² eq170
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  d′² : (₄₊ n) ⊢ P₁₃ CZ • P₁₃ CZ ≈ ε
  d′² = lemma-cong↑ (CZ₂₀ • CZ₂₀) ε CZ₂₀²

------------------------------------------------------------------------
-- (171): the same for the doubly controlled H

private
  PP↓² : (₄₊ n) ⊢ PP ↓ • PP ↓ ≈ ε
  PP↓² = L-sem (PP • PP) ε Eq.refl

  N₂-PP : (₄₊ n) ⊢ N₂.⟪ PP ↓ ⟫ ≈ PP ↓
  N₂-PP {n} = N₂.⟪⟫-fix (sym (L-comm PP X))
    where open Tools ((₄₊ n) VRel,_===_)

  °ΛH-form : (₄₊ n) ⊢ N₂.⟪ ΛH 2 ↓ᵏ n ⟫ ≈ PP ↓ • °box₃ • PP ↓
  °ΛH-form {n} = N₂.⟪⟫-•₃ N₂-PP refl N₂-PP
    where open Tools ((₄₊ n) VRel,_===_)

  -- P ⊗ P below turns the CZ of wires 1 and 3 into the CH: the rule (18)
  -- on the triple 0 1 3.
  PP-d′ : (₄₊ n) ⊢ PP ↓ • P₁₃ CZ • PP ↓ ≈ P₁₃ CH
  PP-d′ {n} = begin
    PP ↓ • P₁₃ CZ • PP ↓
      ≈⟨ sym (cong (M₃-L PP) (cong (M₃-U CZ) (M₃-L PP))) ⟩
    M₃ (L₀ PP) • M₃ (U₀ CZ) • M₃ (L₀ PP)
      ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
    M₃ (L₀ PP • U₀ CZ • L₀ PP)
      ≈⟨ M₃-sem (L₀ PP • U₀ CZ • L₀ PP) (U₀ CH) Eq.refl ⟩
    M₃ (U₀ CH)
      ≈⟨ M₃-U CH ⟩
    P₁₃ CH ∎
    where open Tools ((₄₊ n) VRel,_===_)

  merge-H : ∀ {x y : Circuit (₄₊ n)} → (₄₊ n) ⊢ x • y ≈ P₁₃ CZ →
            (₄₊ n) ⊢ (PP ↓ • x • PP ↓) • (PP ↓ • y • PP ↓) ≈ P₁₃ CH
  merge-H {n} {x} {y} e = begin
    (PP ↓ • x • PP ↓) • (PP ↓ • y • PP ↓)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    PP ↓ • x • (PP ↓ • PP ↓) • y • PP ↓
      ≈⟨ back _ (back _ (cancelˢ _ PP↓²)) ⟩
    PP ↓ • x • y • PP ↓
      ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    PP ↓ • (x • y) • PP ↓
      ≈⟨ back _ (front _ e) ⟩
    PP ↓ • P₁₃ CZ • PP ↓
      ≈⟨ PP-d′ ⟩
    P₁₃ CH ∎
    where open Tools ((₄₊ n) VRel,_===_)

eq171 : (₄₊ n) ⊢ (ΛH 2 ↓ᵏ n) • N₂.⟪ ΛH 2 ↓ᵏ n ⟫ ≈ P₁₃ CH
eq171 {n} = trans (back _ °ΛH-form) (merge-H eq170)
  where open Tools ((₄₊ n) VRel,_===_)

eq171′ : (₄₊ n) ⊢ N₂.⟪ ΛH 2 ↓ᵏ n ⟫ • (ΛH 2 ↓ᵏ n) ≈ P₁₃ CH
eq171′ {n} = trans (front _ °ΛH-form) (merge-H eq170′)
  where open Tools ((₄₊ n) VRel,_===_)
