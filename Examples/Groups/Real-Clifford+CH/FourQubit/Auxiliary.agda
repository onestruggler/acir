------------------------------------------------------------------------
-- Presentations of groups
--
-- Auxiliary equations on four qubits (Clément, Lemma D.5)
--
-- Equations (150)–(248) of Appendix D.3, consequences of Figure 4 given
-- completeness on three qubits (Lemma D.3, the induction hypothesis of
-- the completeness proof).  In progress: (150)–(153).
--
-- Notation of the comments: on the target wire 0, a, p, e are the CH
-- gates controlled by wires 1, 2, 3 and q, b, c the CZ gates; W = CCZX
-- and V = CCXZ are controlled by wires 1 and 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; CZ² ; CH² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (Same)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (CZ₂₀² ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates from wire 3 to wire 0

-- Spelled as in Definition 2.4: the gate on the top pair, carried down
-- by the transposition of wires 0 and 2.
CZ₃₀ CH₃₀ : Circuit (₄₊ n)
CZ₃₀ = τ₀₂-conj (CZ ↑ ↑)
CH₃₀ = τ₀₂-conj (CH ↑ ↑)

CZ₃₀-P : (₄₊ n) ⊢ CZ₃₀ ≈ P₀₃ CZ
CZ₃₀-P = τ-P₀₃ CZ

CH₃₀-P : (₄₊ n) ⊢ CH₃₀ ≈ P₀₃ CH
CH₃₀-P = τ-P₀₃ CH

private
  τ₀₂² : (₄₊ n) ⊢ τ₀₂ • τ₀₂ ≈ ε
  τ₀₂² {n} = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)
    where open Tools ((₄₊ n) VRel,_===_)

CZ₃₀² : (₄₊ n) ⊢ CZ₃₀ • CZ₃₀ ≈ ε
CZ₃₀² {n} = conj-invol τ₀₂² (lemma-cong↑ (CZ ↑ • CZ ↑) ε (lemma-cong↑ (CZ • CZ) ε CZ²))
  where open Tools ((₄₊ n) VRel,_===_)

CH₃₀² : (₄₊ n) ⊢ CH₃₀ • CH₃₀ ≈ ε
CH₃₀² {n} = conj-invol τ₀₂² (lemma-cong↑ (CH ↑ • CH ↑) ε (lemma-cong↑ (CH • CH) ε CH²))
  where open Tools ((₄₊ n) VRel,_===_)

-- The outer CZ passes the one from wire 3: both sit on the triple 0 2 3.
CZ₃₀-CZ₂₀ : (₄₊ n) ⊢ CZ₃₀ • CZ₂₀ ≈ CZ₂₀ • CZ₃₀
CZ₃₀-CZ₂₀ {n} = begin
  CZ₃₀ • CZ₂₀       ≈⟨ front _ CZ₃₀-P ⟩
  P₀₃ CZ • O CZ     ≈⟨ comm-03-02 CZ CZ (evaluated Eq.refl) ⟩
  O CZ • P₀₃ CZ     ≈⟨ back _ (sym CZ₃₀-P) ⟩
  CZ₂₀ • CZ₃₀ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The three-controlled box, at any width from four.
box₃ : Circuit (₄₊ n)
box₃ {n} = Λ□ 3 ↓ᵏ n

------------------------------------------------------------------------
-- (150): the three-controlled box, written out

eq150 : (₄₊ n) ⊢ Λ□ 3 ↓ᵏ n ≈ CH ↓ • CZ₂₀ • CH ↓ • CZ₃₀ • CH ↓ • CZ₂₀ • CH ↓ • CZ₃₀
eq150 {n} = begin
  CCZX • CZ₃₀ • CCXZ • CZ₃₀
    ≈⟨ by-passoc ((□ • □ • □ • □) • □ • (□ • □ • □ • □) • □)
                 (□ • □ • □ • (□ • □ • □) • □ • □ • □ • □) Eq.refl ⟩
  CH ↓ • CZ₂₀ • CH ↓ • (CZ₂₀ • CZ₃₀ • CZ₂₀) • CH ↓ • CZ₂₀ • CH ↓ • CZ₃₀
    ≈⟨ back _ (back _ (back _ (front _ (bzb CZ₂₀² CZ₃₀-CZ₂₀)))) ⟩
  CH ↓ • CZ₂₀ • CH ↓ • CZ₃₀ • CH ↓ • CZ₂₀ • CH ↓ • CZ₃₀ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- What passes the doubly controlled ZX

-- CCZX in three factors on the triples 0 1 3-free… each factor sits on
-- wire 0 and one of the wires 1, 2, or on the pair 1 2: the controlled
-- H Z from wire 1, twice, the controlled H Z from wire 2, and the CNOT
-- from wire 2 to wire 1 that merges the two controls (the paper's proof
-- of (152)).
private
  W-split : (₄₊ n) ⊢ CCZX ≈ L (CH • CZ) • U CX • L (CZ • CH) • U CX • O (CH • CZ)
  W-split {n} = begin
    CCZX
      ≈⟨ L₃-sem CCZX (L₀ (CH • CZ) • U₀ CX • L₀ (CZ • CH) • U₀ CX • O₀ (CH • CZ)) Eq.refl ⟩
    L₃ (L₀ (CH • CZ) • U₀ CX • L₀ (CZ • CH) • U₀ CX • O₀ (CH • CZ))
      ≈⟨ refl ⟩
    L (CH • CZ) • U CX • L (CZ • CH) • U CX • O (CH • CZ) ∎
    where open Tools ((₄₊ n) VRel,_===_)

-- A gate on the pair 0 3 that passes the controlled H Z and Z H from
-- another wire passes CCZX and CCXZ.
W-pass : (u : Circuit 2) →
         Evaluated (O₀ u • L₀ (CH • CZ)) (L₀ (CH • CZ) • O₀ u) →
         Evaluated (O₀ u • L₀ (CZ • CH)) (L₀ (CZ • CH) • O₀ u) →
         (₄₊ n) ⊢ P₀₃ u • CCZX ≈ CCZX • P₀₃ u
W-pass {n} u e₁ e₂ = begin
  P₀₃ u • CCZX
    ≈⟨ back _ W-split ⟩
  P₀₃ u • (L (CH • CZ) • U CX • L (CZ • CH) • U CX • O (CH • CZ))
    ≈⟨ comm-• (comm-03-01 u (CH • CZ) e₁)
      (comm-• (P₀₃-U u CX)
      (comm-• (comm-03-01 u (CZ • CH) e₂)
      (comm-• (P₀₃-U u CX) (comm-03-02 u (CH • CZ) e₁)))) ⟩
  (L (CH • CZ) • U CX • L (CZ • CH) • U CX • O (CH • CZ)) • P₀₃ u
    ≈⟨ front _ (sym W-split) ⟩
  CCZX • P₀₃ u ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

V-pass : (u : Circuit 2) →
         Evaluated (O₀ u • L₀ (CH • CZ)) (L₀ (CH • CZ) • O₀ u) →
         Evaluated (O₀ u • L₀ (CZ • CH)) (L₀ (CZ • CH) • O₀ u) →
         (₄₊ n) ⊢ P₀₃ u • CCXZ ≈ CCXZ • P₀₃ u
V-pass {n} u e₁ e₂ = comm-inv eq117 eq118 (W-pass u e₁ e₂)
  where open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (151), (152)

-- The evaluations, once each: on three wires, the controlled H Z and XZ
-- from wire 2 pass the controlled H Z and Z H from wire 1.
private
  hz₁ : Evaluated (O₀ (CH • CZ) • L₀ (CH • CZ)) (L₀ (CH • CZ) • O₀ (CH • CZ))
  hz₁ = evaluated Eq.refl

  hz₂ : Evaluated (O₀ (CH • CZ) • L₀ (CZ • CH)) (L₀ (CZ • CH) • O₀ (CH • CZ))
  hz₂ = evaluated Eq.refl

  xz₁ : Evaluated (O₀ (Z ↓ • CH • Z ↓ • CH) • L₀ (CH • CZ)) (L₀ (CH • CZ) • O₀ (Z ↓ • CH • Z ↓ • CH))
  xz₁ = evaluated Eq.refl

  xz₂ : Evaluated (O₀ (Z ↓ • CH • Z ↓ • CH) • L₀ (CZ • CH)) (L₀ (CZ • CH) • O₀ (Z ↓ • CH • Z ↓ • CH))
  xz₂ = evaluated Eq.refl

-- The controlled XZ from wire 3.
XZ₃₀ : Circuit (₄₊ n)
XZ₃₀ = P₀₃ (ΛXZ 1)

-- (151)
eq151 : (₄₊ n) ⊢ CCXZ • XZ₃₀ ≈ XZ₃₀ • CCXZ
eq151 {n} = begin
  CCXZ • XZ₃₀                          ≈⟨ back _ form ⟩
  CCXZ • P₀₃ (Z ↓ • CH • Z ↓ • CH)     ≈⟨ sym (V-pass (Z ↓ • CH • Z ↓ • CH) xz₁ xz₂) ⟩
  P₀₃ (Z ↓ • CH • Z ↓ • CH) • CCXZ     ≈⟨ front _ (sym form) ⟩
  XZ₃₀ • CCXZ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  -- The controlled XZ without the swaps of Definition 2.4.
  form : (₄₊ n) ⊢ XZ₃₀ ≈ P₀₃ (Z ↓ • CH • Z ↓ • CH)
  form = P₀₃-sem (ΛXZ 1) (Z ↓ • CH • Z ↓ • CH) Eq.refl

private
  -- The controlled H Z from wire 3.
  ec-P : (₄₊ n) ⊢ CH₃₀ • CZ₃₀ ≈ P₀₃ (CH • CZ)
  ec-P {n} = trans (cong CH₃₀-P CZ₃₀-P) (sym (P₀₃-• CH CZ))
    where open Tools ((₄₊ n) VRel,_===_)

-- (152)
eq152 : (₄₊ n) ⊢ CCZX • CH₃₀ • CZ₃₀ ≈ CH₃₀ • CZ₃₀ • CCZX
eq152 {n} = begin
  CCZX • CH₃₀ • CZ₃₀         ≈⟨ back _ ec-P ⟩
  CCZX • P₀₃ (CH • CZ)       ≈⟨ sym (W-pass (CH • CZ) hz₁ hz₂) ⟩
  P₀₃ (CH • CZ) • CCZX       ≈⟨ front _ (sym ec-P) ⟩
  (CH₃₀ • CZ₃₀) • CCZX       ≈⟨ assoc ⟩
  CH₃₀ • CZ₃₀ • CCZX ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (153): the box with CH in place of CZ

eq153 : (₄₊ n) ⊢ Λ□ 3 ↓ᵏ n ≈ CCZX • CH₃₀ • CCXZ • CH₃₀
eq153 {n} = begin
  CCZX • CZ₃₀ • CCXZ • CZ₃₀
    ≈⟨ back _ cVc ⟩
  CCZX • CH₃₀ • CCXZ • CH₃₀ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  ec-V : (₄₊ n) ⊢ (CH₃₀ • CZ₃₀) • CCXZ ≈ CCXZ • (CH₃₀ • CZ₃₀)
  ec-V = begin
    (CH₃₀ • CZ₃₀) • CCXZ      ≈⟨ front _ ec-P ⟩
    P₀₃ (CH • CZ) • CCXZ      ≈⟨ V-pass (CH • CZ) hz₁ hz₂ ⟩
    CCXZ • P₀₃ (CH • CZ)      ≈⟨ back _ (sym ec-P) ⟩
    CCXZ • (CH₃₀ • CZ₃₀) ∎
  cVc : (₄₊ n) ⊢ CZ₃₀ • CCXZ • CZ₃₀ ≈ CH₃₀ • CCXZ • CH₃₀
  cVc = begin
    CZ₃₀ • CCXZ • CZ₃₀
      ≈⟨ insertˡ _ CH₃₀² ⟩
    CH₃₀ • CH₃₀ • CZ₃₀ • CCXZ • CZ₃₀
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • ((□ • □) • □) • □) Eq.refl ⟩
    CH₃₀ • ((CH₃₀ • CZ₃₀) • CCXZ) • CZ₃₀
      ≈⟨ back _ (front _ ec-V) ⟩
    CH₃₀ • (CCXZ • (CH₃₀ • CZ₃₀)) • CZ₃₀
      ≈⟨ by-passoc (□ • (□ • (□ • □)) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    CH₃₀ • CCXZ • CH₃₀ • (CZ₃₀ • CZ₃₀)
      ≈⟨ back _ (back _ (cancelᵉ _ CZ₃₀²)) ⟩
    CH₃₀ • CCXZ • CH₃₀ ∎
