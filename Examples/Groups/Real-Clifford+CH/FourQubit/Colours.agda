------------------------------------------------------------------------
-- Presentations of groups
--
-- A black control against a white one on four qubits (Clément, Lemma
-- D.5, Equations (179), (180))
--
-- Two gates controlled by the same wire, positively and negatively,
-- commute.  Here: the box with its box wire on wire 1 against the box
-- with its box wire on wire 0 and the control on wire 2 negated, (179),
-- and with the control on wire 3 negated as well, (180).  In progress:
-- (181) onwards.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Colours
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; X²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq176)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq119 ; eq120 ; °CCZX ; °CCXZ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- Disjointness: the lower triple and wire 3

L₃-top : (u : Circuit 3) (v : Circuit (₁₊ n)) → (₄₊ n) ⊢ L₃ u • v ↑ ↑ ↑ ≈ v ↑ ↑ ↑ • L₃ u
L₃-top [ gate₀ () ]ʷ v
L₃-top [ gate₀ () ↥ ]ʷ v
L₃-top [ gate₀ () ↥ ↥ ]ʷ v
L₃-top [ gate₀ () ↥ ↥ ↥ ]ʷ v
L₃-top {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑ ↑))
  where open Tools ((₄₊ n) VRel,_===_)
L₃-top {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h (v ↑))
  where open Tools ((₄₊ n) VRel,_===_)
L₃-top {n} [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h (v ↑)))
  where open Tools ((₃₊ n) VRel,_===_) renaming (sym to PB-sym)
L₃-top {n} [ gate₂ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₂ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₂ h ]ʷ) (PB-sym (comm-gate₂-w↑↑ h v))
  where open Tools ((₃₊ n) VRel,_===_) renaming (sym to PB-sym)
L₃-top {n} [ gate₁ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ↥ ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v)))
  where open Tools ((₂₊ n) VRel,_===_) renaming (sym to PB-sym)
L₃-top {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₄₊ n) VRel,_===_)
L₃-top {n} (u • t) v = begin
  (L₃ u • L₃ t) • v ↑ ↑ ↑   ≈⟨ assoc ⟩
  L₃ u • (L₃ t • v ↑ ↑ ↑)   ≈⟨ back _ (L₃-top t v) ⟩
  L₃ u • (v ↑ ↑ ↑ • L₃ t)   ≈⟨ sym assoc ⟩
  (L₃ u • v ↑ ↑ ↑) • L₃ t   ≈⟨ front _ (L₃-top u v) ⟩
  (v ↑ ↑ ↑ • L₃ u) • L₃ t   ≈⟨ assoc ⟩
  v ↑ ↑ ↑ • (L₃ u • L₃ t) ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (179)

private
  -- The box negated on wire 2, written out.
  N₂-c : (₄₊ n) ⊢ N₂.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
  N₂-c {n} = begin
    N₂.⟪ CZ₃₀ ⟫       ≈⟨ N₂.⟪⟫-cong CZ₃₀-P ⟩
    N₂.⟪ P₀₃ CZ ⟫     ≈⟨ N₂.⟪⟫-fix (sym (P₀₃-U CZ (X ↑))) ⟩
    P₀₃ CZ            ≈⟨ sym CZ₃₀-P ⟩
    CZ₃₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  °box-form : (₄₊ n) ⊢ °box₃ ≈ °CCZX • CZ₃₀ • °CCXZ • CZ₃₀
  °box-form {n} = N₂.⟪⟫-•₄ refl N₂-c refl N₂-c
    where open Tools ((₄₊ n) VRel,_===_)

  °W°V : (₄₊ n) ⊢ °CCZX • °CCXZ ≈ ε
  °W°V {n} = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

  °V°W : (₄₊ n) ⊢ °CCXZ • °CCZX ≈ ε
  °V°W {n} = trans (sym (N₂.⟪⟫-• CCXZ CCZX)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

  -- The box on wire 1 passes the negated CCXZ, (176), and so its inverse.
  B-°V : (₄₊ n) ⊢ box₃′ • °CCXZ ≈ °CCXZ • box₃′
  B-°V {n} = sym eq176
    where open Tools ((₄₊ n) VRel,_===_)

  B-°W : (₄₊ n) ⊢ box₃′ • °CCZX ≈ °CCZX • box₃′
  B-°W {n} = comm-inv °V°W °W°V B-°V
    where open Alg ((₄₊ n) VRel,_===_)

  -- The CZ of wires 1 and 3 passes the box; under the lower swap, the CZ
  -- from wire 3 passes the box on wire 1.
  d′-box : (₄₊ n) ⊢ P₁₃ CZ • box₃ ≈ box₃ • P₁₃ CZ
  d′-box {n} = comm-• d′-W (comm-• d′-c (comm-• d′-V d′-c))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    d′-a : (₄₊ n) ⊢ P₁₃ CZ • CH ↓ ≈ CH ↓ • P₁₃ CZ
    d′-a = sym (comm-01-13 CH CZ (evaluated Eq.refl))
    d′-W : (₄₊ n) ⊢ P₁₃ CZ • CCZX ≈ CCZX • P₁₃ CZ
    d′-W = comm-abab d′-a (P₁₃-O CZ CZ)
    d′-V : (₄₊ n) ⊢ P₁₃ CZ • CCXZ ≈ CCXZ • P₁₃ CZ
    d′-V = comm-inv eq117 eq118 d′-W
    d′-c : (₄₊ n) ⊢ P₁₃ CZ • CZ₃₀ ≈ CZ₃₀ • P₁₃ CZ
    d′-c = begin
      P₁₃ CZ • CZ₃₀       ≈⟨ back _ CZ₃₀-P ⟩
      P₁₃ CZ • P₀₃ CZ     ≈⟨ comm-13-03 CZ CZ (evaluated Eq.refl) ⟩
      P₀₃ CZ • P₁₃ CZ     ≈⟨ front _ (sym CZ₃₀-P) ⟩
      CZ₃₀ • P₁₃ CZ ∎

  B-c : (₄₊ n) ⊢ box₃′ • CZ₃₀ ≈ CZ₃₀ • box₃′
  B-c {n} = begin
    box₃′ • CZ₃₀       ≈⟨ back _ CZ₃₀-P ⟩
    box₃′ • P₀₃ CZ     ≈⟨ sym (S₀₁.⟪⟫-≈ d′-box (S₀₁.⟪⟫-• (P₁₃ CZ) box₃) (S₀₁.⟪⟫-• box₃ (P₁₃ CZ))) ⟩
    P₀₃ CZ • box₃′     ≈⟨ front _ (sym CZ₃₀-P) ⟩
    CZ₃₀ • box₃′ ∎
    where open Tools ((₄₊ n) VRel,_===_)

eq179 : (₄₊ n) ⊢ box₃′ • °box₃ ≈ °box₃ • box₃′
eq179 {n} = begin
  box₃′ • °box₃
    ≈⟨ back _ °box-form ⟩
  box₃′ • (°CCZX • CZ₃₀ • °CCXZ • CZ₃₀)
    ≈⟨ comm-• B-°W (comm-• B-c (comm-• B-°V B-c)) ⟩
  (°CCZX • CZ₃₀ • °CCXZ • CZ₃₀) • box₃′
    ≈⟨ front _ (sym °box-form) ⟩
  °box₃ • box₃′ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (180)

private
  X₃² : (₄₊ n) ⊢ X ↑ ↑ ↑ • X ↑ ↑ ↑ ≈ ε
  X₃² = lemma-cong↑ (X ↑ ↑ • X ↑ ↑) ε (lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²))

-- X on wire 3, as a conjugation.
module N₃ {n : ℕ} = Conj {₄₊ n} (X ↑ ↑ ↑) X₃²

private
  N₃-L₃ : (u : Circuit 3) → (₄₊ n) ⊢ N₃.⟪ L₃ u ⟫ ≈ L₃ u
  N₃-L₃ {n} u = N₃.⟪⟫-fix (sym (L₃-top u X))
    where open Tools ((₄₊ n) VRel,_===_)

  -- The CZ from wire 3, negated there, is that CZ and Z on wire 0: on
  -- the triple 0 2 3, where X on wire 3 is a block of the pair 2 3.
  N₃-c : (₄₊ n) ⊢ N₃.⟪ CZ₃₀ ⟫ ≈ CZ₃₀ • Z ↓
  N₃-c {n} = begin
    N₃.⟪ CZ₃₀ ⟫
      ≈⟨ N₃.⟪⟫-cong CZ₃₀-P ⟩
    X ↑ ↑ ↑ • P₀₃ CZ • X ↑ ↑ ↑
      ≈⟨ sym (cong x₃ (cong (≡⇒≈ (O₃-O CZ)) x₃)) ⟩
    O₃ (U₀ (X ↑)) • O₃ (O₀ CZ) • O₃ (U₀ (X ↑))
      ≈⟨ sym (S₀₁.⟪⟫-•₃ refl refl refl) ⟩
    O₃ (U₀ (X ↑) • O₀ CZ • U₀ (X ↑))
      ≈⟨ O₃-sem (U₀ (X ↑) • O₀ CZ • U₀ (X ↑)) (O₀ CZ • Z ↓) Eq.refl ⟩
    O₃ (O₀ CZ • Z ↓)
      ≈⟨ S₀₁.⟪⟫-• (P₁₃ CZ) (Z ↑) ⟩
    P₀₃ CZ • S₀₁.⟪ Z ↑ ⟫
      ≈⟨ cong (sym CZ₃₀-P) (L-sem (Ex • Z ↑ • Ex) (Z ↓) Eq.refl) ⟩
    CZ₃₀ • Z ↓ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    ≡⇒≈ : ∀ {x y : Circuit (₄₊ n)} → x ≡ y → (₄₊ n) ⊢ x ≈ y
    ≡⇒≈ Eq.refl = refl
    x₃ : (₄₊ n) ⊢ O₃ (U₀ (X ↑)) ≈ X ↑ ↑ ↑
    x₃ = P₂₃-S₀₁ (X ↑)

  -- Z on wire 0 passes the box on wire 1: Z on wire 1 passes the box.
  B-z : (₄₊ n) ⊢ box₃′ • Z ↓ ≈ Z ↓ • box₃′
  B-z {n} = begin
    box₃′ • Z ↓
      ≈⟨ back _ (sym (L-sem (Ex • Z ↑ • Ex) (Z ↓) Eq.refl)) ⟩
    box₃′ • S₀₁.⟪ Z ↑ ⟫
      ≈⟨ sym (S₀₁.⟪⟫-≈ z₁-box (S₀₁.⟪⟫-• (Z ↑) box₃) (S₀₁.⟪⟫-• box₃ (Z ↑))) ⟩
    S₀₁.⟪ Z ↑ ⟫ • box₃′
      ≈⟨ front _ (L-sem (Ex • Z ↑ • Ex) (Z ↓) Eq.refl) ⟩
    Z ↓ • box₃′ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    z₁-c : (₄₊ n) ⊢ Z ↑ • CZ₃₀ ≈ CZ₃₀ • Z ↑
    z₁-c = begin
      Z ↑ • CZ₃₀         ≈⟨ back _ CZ₃₀-P ⟩
      U (Z ↓) • P₀₃ CZ   ≈⟨ sym (P₀₃-U CZ (Z ↓)) ⟩
      P₀₃ CZ • U (Z ↓)   ≈⟨ front _ (sym CZ₃₀-P) ⟩
      CZ₃₀ • Z ↑ ∎
    z₁-box : (₄₊ n) ⊢ Z ↑ • box₃ ≈ box₃ • Z ↑
    z₁-box = comm-• eq119 (comm-• z₁-c (comm-• eq120 z₁-c))

-- The box negated on wires 2 and 3.
°°box₃ : Circuit (₄₊ n)
°°box₃ = N₃.⟪ °box₃ ⟫

eq180 : (₄₊ n) ⊢ box₃′ • °°box₃ ≈ °°box₃ • box₃′
eq180 {n} = begin
  box₃′ • °°box₃
    ≈⟨ back _ form ⟩
  box₃′ • (°CCZX • (CZ₃₀ • Z ↓) • °CCXZ • (CZ₃₀ • Z ↓))
    ≈⟨ comm-• B-°W (comm-• B-cz (comm-• B-°V B-cz)) ⟩
  (°CCZX • (CZ₃₀ • Z ↓) • °CCXZ • (CZ₃₀ • Z ↓)) • box₃′
    ≈⟨ front _ (sym form) ⟩
  °°box₃ • box₃′ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  form : (₄₊ n) ⊢ °°box₃ ≈ °CCZX • (CZ₃₀ • Z ↓) • °CCXZ • (CZ₃₀ • Z ↓)
  form = trans (N₃.⟪⟫-cong °box-form)
    (N₃.⟪⟫-•₄ (N₃-L₃ °CCZX) N₃-c (N₃-L₃ °CCXZ) N₃-c)
  B-cz : (₄₊ n) ⊢ box₃′ • (CZ₃₀ • Z ↓) ≈ (CZ₃₀ • Z ↓) • box₃′
  B-cz = comm-• B-c B-z
