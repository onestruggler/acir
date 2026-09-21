------------------------------------------------------------------------
-- Presentations of groups
--
-- The first auxiliary equations on five qubits (Clément, Lemma D.7,
-- Equations (249)–(252))
--
-- Five wires is where the schema (19) enters: the four-controlled box
-- W B V B — W the doubly controlled ZX on wire 0, B the three-controlled
-- box on the wires 0 1 3 4 with its box wire on wire 1 — passes Z on
-- wire 0.  Z turns W and V into each other and passes B (wire 0 is a
-- control of B), so (19) says V B W B = W B V B, that is, W² passes B;
-- and W² is the CZ of the wires 1 2, (16).  So (19) is: the box passes
-- a CZ between its box wire and the fifth wire.  Under the transposition
-- of the wires 0 and 2 this is (249).
--
-- (251): the box does not depend on its box wire.  The swap of the
-- wires 0 1 is a word in CZ and H on those wires, (8); the box on the
-- wires 1–4 passes the CZ by (249), H on its box wire by (155), and H
-- on wire 0, which it does not touch.
--
-- (250): P ⊗ P on the box wire and the fifth wire leaves the box alone.
-- It turns the letters of the box W c V c into those of its form (153),
-- mirrored — W and V into each other by (174), the CZ from wire 4, spelt
-- from the pair 1 2 upwards, into the CH by the rule (18).
--
-- (252): the doubly controlled H does not depend on its box wire either.
-- It is the box between P ⊗ P on its H wire and its box wire; moving the
-- box wire changes that P ⊗ P by the one on the wires 0 1 — the Klein
-- four-group —, which (250) absorbs.
--
-- (19) is stated at the width of its box; `TopWeakening` carries it to
-- the bottom wires of any wider circuit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Auxiliary
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; Z² ; H² ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (box-Z₅)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CH₃₀ ; CZ₃₀-P ; CH₃₀-P ; eq153)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq155 ; eq166 ; CZ↑-CH₃₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (eq174)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (Ex₂²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₁² ; klein-ca)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₀₂ ; PP₁₂² ; PP₀₂² ; PP-triangle₂)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq119 ; eq120 ; eq123 ; eq124 ; CCZX² ; PP-CZ↑)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The four-controlled box, its box wire on wire 0.
box₄ : Circuit (₁₊ (₄₊ n))
box₄ {n} = Λ□ 4 ↓ᵏ n

-- The three-controlled box on the wires 1–4, its box wire on wire 1.
box₃↑ : Circuit (₁₊ (₄₊ n))
box₃↑ = box₃ ↑

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  -- A letter pushed through four others.
  push₄ : ∀ {x a b c d a′ b′ c′ d′ : Word X} →
          x • a ≈ a′ • x → x • b ≈ b′ • x → x • c ≈ c′ • x → x • d ≈ d′ • x →
          x • (a • b • c • d) ≈ (a′ • b′ • c′ • d′) • x
  push₄ {x} {a} {b} {c} {d} {a′} {b′} {c′} {d′} xa xb xc xd = begin
    x • (a • b • c • d)       ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (x • a) • b • c • d       ≈⟨ front _ xa ⟩
    (a′ • x) • b • c • d      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
    a′ • (x • b) • c • d      ≈⟨ back _ (front _ xb) ⟩
    a′ • (b′ • x) • c • d     ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    a′ • b′ • (x • c) • d     ≈⟨ back _ (back _ (front _ xc)) ⟩
    a′ • b′ • (c′ • x) • d    ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    a′ • b′ • c′ • (x • d)    ≈⟨ back _ (back _ (back _ xd)) ⟩
    a′ • b′ • c′ • (d′ • x)   ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
    (a′ • b′ • c′ • d′) • x ∎

  -- The content of (19): if an involution z turns W and V into each
  -- other and passes B and the box W B V B, then W² passes B.
  square-passes : ∀ {z W V B : Word X} →
                  z • z ≈ ε → W • V ≈ ε → V • W ≈ ε → B • B ≈ ε →
                  z • W ≈ V • z → z • V ≈ W • z → z • B ≈ B • z →
                  z • (W • B • V • B) ≈ (W • B • V • B) • z →
                  (W • W) • B ≈ B • (W • W)
  square-passes {z} {W} {V} {B} zz WV VW BB zW zV zB zQ = sym (begin
    B • (W • W)
      ≈⟨ by-passoc (□ • (□ • □)) (□ • □ • □) Eq.refl ⟩
    B • W • W
      ≈⟨ back _ (back _ (sym left-unit)) ⟩
    B • W • ε • W
      ≈⟨ back _ (back _ (front _ (sym BB))) ⟩
    B • W • (B • B) • W
      ≈⟨ by-passoc (□ • □ • (□ • □) • □) ((□ • □ • □) • □ • □) Eq.refl ⟩
    (B • W • B) • B • W
      ≈⟨ front _ e₁ ⟩
    (W • W • B • V • B) • B • W
      ≈⟨ by-passoc ((□ • □ • □ • □ • □) • □ • □) (□ • □ • □ • □ • (□ • □) • □) Eq.refl ⟩
    W • W • B • V • (B • B) • W
      ≈⟨ back _ (back _ (back _ (back _ (cancelˢ _ BB)))) ⟩
    W • W • B • V • W
      ≈⟨ back _ (back _ (back _ VW)) ⟩
    W • W • B • ε
      ≈⟨ back _ (back _ right-unit) ⟩
    W • W • B
      ≈⟨ sym assoc ⟩
    (W • W) • B ∎)
    where
    -- (19) with z pushed through and cancelled.
    e : V • B • W • B ≈ W • B • V • B
    e = begin
      V • B • W • B                 ≈⟨ sym right-unit ⟩
      (V • B • W • B) • ε           ≈⟨ back _ (sym zz) ⟩
      (V • B • W • B) • z • z       ≈⟨ sym assoc ⟩
      ((V • B • W • B) • z) • z     ≈⟨ front _ (sym (push₄ zW zB zV zB)) ⟩
      (z • (W • B • V • B)) • z     ≈⟨ front _ zQ ⟩
      ((W • B • V • B) • z) • z     ≈⟨ cancelʳ _ zz ⟩
      W • B • V • B ∎

    e₁ : B • W • B ≈ W • W • B • V • B
    e₁ = begin
      B • W • B                     ≈⟨ sym left-unit ⟩
      ε • B • W • B                 ≈⟨ front _ (sym WV) ⟩
      (W • V) • B • W • B           ≈⟨ assoc ⟩
      W • V • B • W • B             ≈⟨ back _ e ⟩
      W • W • B • V • B ∎

------------------------------------------------------------------------
-- (249)

private
  -- Z on a control of the four-wire box.
  z₁-c : (₄₊ n) ⊢ Z ↑ • CZ₃₀ ≈ CZ₃₀ • Z ↑
  z₁-c {n} = begin
    Z ↑ • CZ₃₀         ≈⟨ back _ CZ₃₀-P ⟩
    U (Z ↓) • P₀₃ CZ   ≈⟨ sym (P₀₃-U CZ (Z ↓)) ⟩
    P₀₃ CZ • U (Z ↓)   ≈⟨ front _ (sym CZ₃₀-P) ⟩
    CZ₃₀ • Z ↑ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  z₁-box : (₄₊ n) ⊢ Z ↑ • box₃ ≈ box₃ • Z ↑
  z₁-box {n} = comm-• eq119 (comm-• z₁-c (comm-• eq120 z₁-c))
    where open Alg ((₄₊ n) VRel,_===_)

  -- A gate from wire 3 to wire 0, spelled from the pair 0 1 upwards.
  spell : (u : Circuit 2) → (₄₊ n) ⊢ P₀₃ u ≈ S₂₃.⟪ S₁₂.⟪ L u ⟫ ⟫
  spell {n} u = sym (trans (S₂₃.⟪⟫-cong (O-L u)) (O-S₂₃ u))
    where open Tools ((₄₊ n) VRel,_===_)

  CZ₃₀-spell : (₄₊ n) ⊢ CZ₃₀ ≈ S₂₃.⟪ S₁₂.⟪ CZ ↓ ⟫ ⟫
  CZ₃₀-spell {n} = trans CZ₃₀-P (spell CZ)
    where open Tools ((₄₊ n) VRel,_===_)

  CH₃₀-spell : (₄₊ n) ⊢ CH₃₀ ≈ S₂₃.⟪ S₁₂.⟪ CH ↓ ⟫ ⟫
  CH₃₀-spell {n} = trans CH₃₀-P (spell CH)
    where open Tools ((₄₊ n) VRel,_===_)

  -- The box in its form (153), mirrored.
  mirror₄ : (₄₊ n) ⊢ CCXZ • CH₃₀ • CCZX • CH₃₀ ≈ box₃
  mirror₄ {n} = begin
    CCXZ • CH₃₀ • CCZX • CH₃₀       ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (CCXZ • CH₃₀ • CCZX) • CH₃₀     ≈⟨ front _ (flip-WcV (sym eq124) V-dW CZ↑-CH₃₀) ⟩
    (CCZX • CH₃₀ • CCXZ) • CH₃₀     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    CCZX • CH₃₀ • CCXZ • CH₃₀       ≈⟨ sym eq153 ⟩
    box₃ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    V-dW : CCXZ ≈ CZ ↑ • CCZX
    V-dW = begin
      CCXZ                      ≈⟨ sym eq124 ⟩
      CCZX • CZ ↑               ≈⟨ back _ (sym CCZX²) ⟩
      CCZX • CCZX • CCZX        ≈⟨ sym assoc ⟩
      (CCZX • CCZX) • CCZX      ≈⟨ front _ CCZX² ⟩
      CZ ↑ • CCZX ∎

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    B : Circuit (₁₊ (₄₊ n))
    B = τ₀₂-conj box₃↑

    τ₀₂² : τ₀₂ • τ₀₂ ≈ ε
    τ₀₂² = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)

    module T = Conj {₁₊ (₄₊ n)} τ₀₂ τ₀₂²

    box₃↑² : box₃↑ • box₃↑ ≈ ε
    box₃↑² = lemma-cong↑ (box₃ • box₃) ε eq166

    B² : B • B ≈ ε
    B² = T.⟪⟫-invol box₃↑²

    -- Z on wire 0 is, under the transposition, Z on wire 2: a control of
    -- the box on the wires 1–4.
    T-Z : T.⟪ Z ↑ ↑ ⟫ ≈ Z ↓
    T-Z = L₃-sem (τ₀₂ • Z ↑ ↑ • τ₀₂) (Z ↓) Eq.refl

    z-B : Z ↓ • B ≈ B • Z ↓
    z-B = T.⟪⟫-≈ (lemma-cong↑ (Z ↑ • box₃) (box₃ • Z ↑) z₁-box)
                 (T.⟪⟫-•₂ T-Z refl) (T.⟪⟫-•₂ refl T-Z)

    z-W : Z ↓ • CCZX ≈ CCXZ • Z ↓
    z-W = sym (conj-comm Z² (trans (sym assoc) (trans (front _ eq123) (cancelʳ _ Z²))))

    -- (19), read as a statement about W².
    W²-B : CZ ↑ • B ≈ B • CZ ↑
    W²-B = trans (front _ (sym CCZX²))
           (trans (square-passes Γ Z² eq117 eq118 B² z-W eq123 z-B (box-Z₅ n))
                  (back _ CCZX²))

    T-CZ : T.⟪ CZ ↑ ⟫ ≈ CZ ↓
    T-CZ = L₃-sem (τ₀₂ • CZ ↑ • τ₀₂) (CZ ↓) Eq.refl

  -- (249)
  eq249 : CZ ↓ • box₃↑ ≈ box₃↑ • CZ ↓
  eq249 = T.⟪⟫-≈ W²-B (T.⟪⟫-•₂ T-CZ (T.⟪⟫-⟪⟫ box₃↑)) (T.⟪⟫-•₂ (T.⟪⟫-⟪⟫ box₃↑) T-CZ)

  ----------------------------------------------------------------------
  -- (251)

  private
    h₀-box : H ↓ • box₃↑ ≈ box₃↑ • H ↓
    h₀-box = sym (comm-gate₁-w↑ H-gate box₃)

    h₁-box : H ↑ • box₃↑ ≈ box₃↑ • H ↑
    h₁-box = lemma-cong↑ (H ↓ • box₃) (box₃ • H ↓) eq155

    t-box : (CZ • H ↓ • H ↑) • box₃↑ ≈ box₃↑ • (CZ • H ↓ • H ↑)
    t-box = sym (comm-• (sym eq249) (comm-• (sym h₀-box) (sym h₁-box)))

  -- The swap of the wires 0 1 passes the box on the wires 1–4 …
  Ex-box₃↑ : Ex ↓ • box₃↑ ≈ box₃↑ • Ex ↓
  Ex-box₃↑ = begin
    (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • box₃↑
      ≈⟨ front _ (by-passoc (□ • □ • □ • □ • □ • □ • □ • □ • □)
                            ((□ • □ • □) • (□ • □ • □) • (□ • □ • □)) Eq.refl) ⟩
    ((CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑)) • box₃↑
      ≈⟨ sym (comm-• (sym t-box) (comm-• (sym t-box) (sym t-box))) ⟩
    box₃↑ • ((CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑) • (CZ • H ↓ • H ↑))
      ≈⟨ back _ (by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □))
                           (□ • □ • □ • □ • □ • □ • □ • □ • □) Eq.refl) ⟩
    box₃↑ • Ex ↓ ∎

  -- … so the box with its box wire on wire 0 is the box with its box
  -- wire on wire 1.
  eq251 : box₃↑ ≈ Ex ↓ • box₃↑ • Ex ↓
  eq251 = sym (S.⟪⟫-fix Ex-box₃↑)
    where module S = Conj {₁₊ (₄₊ n)} (Ex ↓) Ex²

  ----------------------------------------------------------------------
  -- (250)

  private
    W′ V′ c′ h′ : Circuit (₁₊ (₄₊ n))
    W′ = CCZX ↑
    V′ = CCXZ ↑
    c′ = CZ₃₀ ↑
    h′ = CH₃₀ ↑

    Ex₃² : Ex ↑ ↑ ↑ • Ex ↑ ↑ ↑ ≈ ε
    Ex₃² = lemma-cong↑ (Ex ↑ ↑ • Ex ↑ ↑) ε Ex₂²

    module Pj  = Conj {₁₊ (₄₊ n)} PP₀₁ PP₀₁²
    module S₃₄ = Conj {₁₊ (₄₊ n)} (Ex ↑ ↑ ↑) Ex₃²

    conj-swap : ∀ {x y : Circuit (₁₊ (₄₊ n))} → x • y ≈ y • x → (w : Circuit (₁₊ (₄₊ n))) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    conj-pass : ∀ {x w w′ : Circuit (₁₊ (₄₊ n))} → x • x ≈ ε → x • w • x ≈ w′ → x • w ≈ w′ • x
    conj-pass {x} {w} {w′} xx e = begin
      x • w                 ≈⟨ sym right-unit ⟩
      (x • w) • ε           ≈⟨ back _ (sym xx) ⟩
      (x • w) • x • x       ≈⟨ by-passoc ((□ • □) • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (x • w • x) • x       ≈⟨ front _ e ⟩
      w′ • x ∎

    -- The gates from wire 4 to wire 1, spelled from the pair 1 2 upwards,
    -- so that P ⊗ P on the wires 0 1 meets only the CZ of the wires 1 2:
    -- the rule (18).
    c′-spell : c′ ≈ S₃₄.⟪ S₂₃.⟪ CZ ↑ ⟫ ⟫
    c′-spell = lemma-cong↑ CZ₃₀ (S₂₃.⟪ S₁₂.⟪ CZ ↓ ⟫ ⟫) CZ₃₀-spell

    h′-spell : h′ ≈ S₃₄.⟪ S₂₃.⟪ CH ↑ ⟫ ⟫
    h′-spell = lemma-cong↑ CH₃₀ (S₂₃.⟪ S₁₂.⟪ CH ↓ ⟫ ⟫) CH₃₀-spell

    Pj-c′ : Pj.⟪ c′ ⟫ ≈ h′
    Pj-c′ = begin
      Pj.⟪ c′ ⟫
        ≈⟨ Pj.⟪⟫-cong c′-spell ⟩
      Pj.⟪ S₃₄.⟪ S₂₃.⟪ CZ ↑ ⟫ ⟫ ⟫
        ≈⟨ conj-swap (L-comm PP (Ex ↑)) (S₂₃.⟪ CZ ↑ ⟫) ⟩
      S₃₄.⟪ Pj.⟪ S₂₃.⟪ CZ ↑ ⟫ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (conj-swap (L-comm PP Ex) (CZ ↑)) ⟩
      S₃₄.⟪ S₂₃.⟪ Pj.⟪ CZ ↑ ⟫ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong PP-CZ↑) ⟩
      S₃₄.⟪ S₂₃.⟪ CH ↑ ⟫ ⟫
        ≈⟨ sym h′-spell ⟩
      h′ ∎

    pp-V′ : PP₀₁ • V′ ≈ W′ • PP₀₁
    pp-V′ = sym (conj-comm PP₀₁² (trans (sym assoc) (trans (front _ eq174) (cancelʳ _ PP₀₁²))))

    pp-c′ : PP₀₁ • c′ ≈ h′ • PP₀₁
    pp-c′ = conj-pass PP₀₁² Pj-c′

    PP-box : PP₀₁ • box₃↑ ≈ box₃↑ • PP₀₁
    PP-box = begin
      PP₀₁ • (W′ • c′ • V′ • c′)      ≈⟨ push₄ Γ eq174 pp-c′ pp-V′ pp-c′ ⟩
      (V′ • h′ • W′ • h′) • PP₀₁      ≈⟨ front _ (lemma-cong↑ (CCXZ • CH₃₀ • CCZX • CH₃₀) box₃ mirror₄) ⟩
      box₃↑ • PP₀₁ ∎

  -- P ⊗ P on the box wire and the fifth wire leaves the box alone.
  eq250 : PP₀₁ • box₃↑ • PP₀₁ ≈ box₃↑
  eq250 = Pj.⟪⟫-fix PP-box

  ----------------------------------------------------------------------
  -- (252)

  -- The doubly controlled H on the wires 1–4: H on wire 2, box wire 1.
  ΛH₂↑ : Circuit (₁₊ (₄₊ n))
  ΛH₂↑ = (ΛH 2 ↓ᵏ n) ↑

  -- Its box wire moved to wire 0: the two P ⊗ P differ by the one on the
  -- wires 0 1 — the Klein four-group —, which (250) absorbs.
  eq252 : ΛH₂↑ ≈ Ex ↓ • ΛH₂↑ • Ex ↓
  eq252 = sym (begin
    S₀₁.⟪ PP₁₂ • box₃↑ • PP₁₂ ⟫
      ≈⟨ S₀₁.⟪⟫-•₃ refl (sym eq251) refl ⟩
    PP₀₂ • box₃↑ • PP₀₂
      ≈⟨ cong (sym (klein-ca Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂)) (back _ (sym PP-triangle₂)) ⟩
    (PP₁₂ • PP₀₁) • box₃↑ • (PP₀₁ • PP₁₂)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    PP₁₂ • (PP₀₁ • box₃↑ • PP₀₁) • PP₁₂
      ≈⟨ back _ (front _ eq250) ⟩
    PP₁₂ • box₃↑ • PP₁₂ ∎)
