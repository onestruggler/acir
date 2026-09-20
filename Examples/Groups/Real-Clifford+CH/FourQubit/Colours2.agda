------------------------------------------------------------------------
-- Presentations of groups
--
-- Consequences of Equation (181) (Clément, Lemma D.5, Equations
-- (182)–(190))
--
-- The paper: "Equations (182) to (189) follow directly from Equation
-- (181) together with Equations (81), (157), (161)" — (181) carried
-- along a permutation of the wires, the controls of a box exchanged,
-- and a control's colour changed by X.  A gate placed by Definition 2.4
-- is a conjugate of the base gate by swaps (and by X on its white
-- controls); transporting an equation along an involution is
-- Conj.⟪⟫-≈.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Colours2
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CH₃₀-P ; CH₃₀²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals181 complete₂ complete₃
  using (ev-17)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
  using (O₃-comm-ev)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq157 ; eq161)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq177)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; ΛH₂′-rot′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq117 ; eq118 ; °CCZX ; °CCXZ ; °CZ₂₀-O)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- X on wire 2 and the lower swap

private
  N₂-Ex : (₄₊ n) ⊢ N₂.⟪ Ex ↓ ⟫ ≈ Ex ↓
  N₂-Ex {n} = N₂.⟪⟫-fix (sym (L-comm Ex X))
    where open Tools ((₄₊ n) VRel,_===_)

-- The box on wire 1, negated on wire 2, is the negated box under the
-- lower swap.
N₂-box₃′ : (₄₊ n) ⊢ N₂.⟪ box₃′ ⟫ ≈ S₀₁.⟪ °box₃ ⟫
N₂-box₃′ {n} = N₂.⟪⟫-•₃ N₂-Ex refl N₂-Ex
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (182)

-- The doubly controlled H with its H on wire 1, its box wire on wire 3
-- and its controls on wires 0 and 2, against the box negated on wire 2:
-- (181) with the colours on wire 2 exchanged, under the lower swap.
eq182 : (₄₊ n) ⊢ S₀₁.⟪ ΛH₂′ ⟫ • °box₃ ≈ °box₃ • S₀₁.⟪ ΛH₂′ ⟫
eq182 {n} = sym (S₀₁.⟪⟫-≈ black
  (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ °box₃) refl)
  (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ °box₃)))
  where
  open Tools ((₄₊ n) VRel,_===_)
  -- (181) with the colours exchanged.
  black : (₄₊ n) ⊢ S₀₁.⟪ °box₃ ⟫ • ΛH₂′ ≈ ΛH₂′ • S₀₁.⟪ °box₃ ⟫
  black = N₂.⟪⟫-≈ eq181
    (N₂.⟪⟫-•₂ N₂-box₃′ (N₂.⟪⟫-⟪⟫ ΛH₂′))
    (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ ΛH₂′) N₂-box₃′)

------------------------------------------------------------------------
-- (183)–(189)

-- Each is (181), or (181) with the colours on the shared wire exchanged
-- (`eq181ᵇ`), carried along a permutation of the wires.  The gates are
-- spelled as the conjugates this produces, simplified where a symmetry
-- already proved applies: in Definition 2.4's placement the same gate is
-- the conjugate by another network of swaps for the same permutation,
-- equal to this one by the relations of the symmetric group and the
-- symmetry of the box in its controls, (157) and (161).
--
-- Writing H(h, t; …) for the doubly controlled H with its H on wire h and
-- its box wire on wire t, and Box(u; …) for the box with box wire u, a °
-- marking a white control:
--
--   (181) = (188)   Box(1; 0, 2, 3)     H(0, 3; 1, °2)
--   (182)           H(1, 3; 0, 2)       Box(0; 1, °2, 3)
--   (183)           H(1, 0; 2, 3)       Box(2; 0, 1, °3)
--   (184)           Box(0; 1, 2, 3)     H(2, 1; 0, °3)
--   (185)           Box(2; 0, 1, 3)     H(0, 1; 2, °3)
--   (186)           H(0, 3; 1, 2)       Box(2; 0, °1, 3)
--   (187)           H(0, 1; 2, 3)       Box(3; 0, 1, °2)
--   (189)           H(0, 1; 2, 3)       Box(2; 0, 1, °3)

private
  Ex₁² : (₄₊ n) ⊢ Ex ↑ • Ex ↑ ≈ ε
  Ex₁² = lemma-cong↑ (Ex • Ex) ε Ex²

  Ex₂² : (₄₊ n) ⊢ Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
  Ex₂² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

-- Transporting a commutation along an involution.
tr : ∀ {c x y : Circuit (₄₊ n)} → (₄₊ n) ⊢ c • c ≈ ε → (₄₊ n) ⊢ x • y ≈ y • x →
     (₄₊ n) ⊢ (c • x • c) • (c • y • c) ≈ (c • y • c) • (c • x • c)
tr {n} {c} {x} {y} cc e = C.⟪⟫-≈ e (C.⟪⟫-• x y) (C.⟪⟫-• y x)
  where module C = Conj c cc

-- (181) with the colours exchanged: the H gate black, the box white.
eq181ᵇ : (₄₊ n) ⊢ S₀₁.⟪ °box₃ ⟫ • ΛH₂′ ≈ ΛH₂′ • S₀₁.⟪ °box₃ ⟫
eq181ᵇ {n} = N₂.⟪⟫-≈ eq181
  (N₂.⟪⟫-•₂ N₂-box₃′ (N₂.⟪⟫-⟪⟫ ΛH₂′))
  (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ ΛH₂′) N₂-box₃′)

-- (183): along the cycle that takes wire 3 to wire 0, which carries the H
-- gate back to ΛH 2.
eq183 : (₄₊ n) ⊢ (ΛH 2 ↓ᵏ n) • S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫
               ≈ S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫ • (ΛH 2 ↓ᵏ n)
eq183 {n} = begin
  (ΛH 2 ↓ᵏ n) • Bx
    ≈⟨ front _ (sym back-home) ⟩
  S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ ⟫ • Bx
    ≈⟨ sym (tr Ex² (tr Ex₁² (tr Ex₂² eq181ᵇ))) ⟩
  Bx • S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ ⟫
    ≈⟨ back _ back-home ⟩
  Bx • (ΛH 2 ↓ᵏ n) ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  Bx : Circuit (₄₊ n)
  Bx = S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫
  back-home : (₄₊ n) ⊢ S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ ⟫ ≈ ΛH 2 ↓ᵏ n
  back-home = trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ _)))
             (trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ _)) (S₀₁.⟪⟫-⟪⟫ _))

-- (184): the box comes back to its base position.
eq184 : (₄₊ n) ⊢ box₃ • S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ⟫
               ≈ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ⟫ • box₃
eq184 {n} = begin
  box₃ • Hx
    ≈⟨ front _ (sym home) ⟩
  S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ box₃′ ⟫ ⟫ ⟫ • Hx
    ≈⟨ tr Ex₁² (tr Ex₂² (tr Ex² eq181)) ⟩
  Hx • S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ box₃′ ⟫ ⟫ ⟫
    ≈⟨ back _ home ⟩
  Hx • box₃ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  Hx : Circuit (₄₊ n)
  Hx = S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ⟫
  home : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ box₃′ ⟫ ⟫ ⟫ ≈ box₃
  home = trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ box₃)))
        (trans (S₁₂.⟪⟫-cong eq161) eq157)

-- (185)
eq185 : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ box₃′ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ °ΛH₂′ ⟫ ⟫
               ≈ S₁₂.⟪ S₂₃.⟪ °ΛH₂′ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ box₃′ ⟫ ⟫
eq185 = tr Ex₁² (tr Ex₂² eq181)

-- (186)
eq186 : (₄₊ n) ⊢ S₁₂.⟪ ΛH₂′ ⟫ • S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫
               ≈ S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ • S₁₂.⟪ ΛH₂′ ⟫
eq186 {n} = sym (tr Ex₁² eq181ᵇ)
  where open Tools ((₄₊ n) VRel,_===_)

-- (187): wires 1 and 3 exchanged.
eq187 : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ ΛH₂′ ⟫ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫
               ≈ S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ ΛH₂′ ⟫ ⟫ ⟫
eq187 {n} = sym (tr Ex₁² (tr Ex₂² (tr Ex₁² eq181ᵇ)))
  where open Tools ((₄₊ n) VRel,_===_)

-- (188) is drawn as (181).
eq188 : (₄₊ n) ⊢ box₃′ • °ΛH₂′ ≈ °ΛH₂′ • box₃′
eq188 = eq181

-- (189)
eq189 : (₄₊ n) ⊢ S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫
               ≈ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ • S₁₂.⟪ S₂₃.⟪ ΛH₂′ ⟫ ⟫
eq189 {n} = sym (tr Ex₁² (tr Ex₂² eq181ᵇ))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (190): the H gate on the box wire of a box of the other colour

-- H(0, 3; 1, 2) against Box(0; 1, °2, 3): the H now sits on the box wire
-- of the box.  By (177), negated on wire 2, that box is °W °B °V °B with
-- °W the negated CCZX and °B = Box(1; 0, °2, 3).  The H gate passes °B,
-- (181) with the colours exchanged; and it passes °W = a °b a °b factor
-- by factor — the lower CH a plainly, and the CZ °b from wire 2, negated
-- there, by the rule (17) on the wires 0 ← 3 ← 2, with the rotation of
-- the H gate written over the CH from wire 2 (`ΛH₂′-rot′`).
module _ {n : ℕ} where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

  private
    a °b d′ h₃ e′ R′ R′⁻ : Circuit (₄₊ n)
    a   = CH ↓
    °b  = °CZ₂₀
    d′  = P₁₃ CZ
    h₃  = P₂₃ HC
    e′  = P₀₃ CH
    R′  = d′ • h₃ • d′ • h₃
    R′⁻ = h₃ • d′ • h₃ • d′

    e′² : e′ • e′ ≈ ε
    e′² = trans (cong (sym CH₃₀-P) (sym CH₃₀-P)) CH₃₀²

    -- The lower CH passes the H gate.
    a-d′ : a • d′ ≈ d′ • a
    a-d′ = comm-01-13 CH CZ (evaluated Eq.refl)

    a-h₃ : a • h₃ ≈ h₃ • a
    a-h₃ = sym (P₂₃-L HC CH)

    a-e′ : a • e′ ≈ e′ • a
    a-e′ = comm-01-03 CH CH (evaluated Eq.refl)

    a-G : a • ΛH₂′ ≈ ΛH₂′ • a
    a-G = begin
      a • ΛH₂′                        ≈⟨ back _ ΛH₂′-rot′ ⟩
      a • (R′ • e′ • R′⁻ • e′)        ≈⟨ comm-• (comm-abab a-d′ a-h₃)
                                           (comm-• a-e′ (comm-• (comm-abab a-h₃ a-d′) a-e′)) ⟩
      (R′ • e′ • R′⁻ • e′) • a        ≈⟨ front _ (sym ΛH₂′-rot′) ⟩
      ΛH₂′ • a ∎

    -- So does the CZ from wire 2 negated there.
    °b-d′ : °b • d′ ≈ d′ • °b
    °b-d′ = begin
      °b • d′         ≈⟨ front _ °CZ₂₀-O ⟩
      O °CZ • d′      ≈⟨ sym (P₁₃-O CZ °CZ) ⟩
      d′ • O °CZ      ≈⟨ back _ (sym °CZ₂₀-O) ⟩
      d′ • °b ∎

    °b-h₃ : °b • h₃ ≈ h₃ • °b
    °b-h₃ = begin
      °b • h₃         ≈⟨ front _ °CZ₂₀-O ⟩
      O °CZ • h₃      ≈⟨ comm-02-23 °CZ HC (evaluated Eq.refl) ⟩
      h₃ • O °CZ      ≈⟨ back _ (sym °CZ₂₀-O) ⟩
      h₃ • °b ∎

  private module E′ = Conj {₄₊ n} e′ e′²

  private
    ĥ : Circuit (₄₊ n)
    ĥ = E′.⟪ h₃ ⟫

    E-d′ : E′.⟪ d′ ⟫ ≈ d′
    E-d′ = E′.⟪⟫-fix (sym (comm-13-03 CZ CH (evaluated Eq.refl)))

    tail-form : e′ • R′⁻ • e′ ≈ ĥ • d′ • ĥ • d′
    tail-form = E′.⟪⟫-•₄ refl E-d′ refl E-d′

    -- The rule (17) on the triple 0 2 3.
    °b-ĥ : °b • ĥ ≈ ĥ • °b
    °b-ĥ = begin
      °b • (e′ • h₃ • e′)
        ≈⟨ cong °CZ₂₀-O (sym (S₀₁.⟪⟫-•₃ refl (P₂₃-S₀₁ HC) refl)) ⟩
      O₃ (L₀ °CZ) • O₃ (O₀ CH • U₀ HC • O₀ CH)
        ≈⟨ O₃-comm-ev ev-17 ⟩
      O₃ (O₀ CH • U₀ HC • O₀ CH) • O₃ (L₀ °CZ)
        ≈⟨ cong (S₀₁.⟪⟫-•₃ refl (P₂₃-S₀₁ HC) refl) (sym °CZ₂₀-O) ⟩
      (e′ • h₃ • e′) • °b ∎

    °b-tail : °b • (e′ • R′⁻ • e′) ≈ (e′ • R′⁻ • e′) • °b
    °b-tail = begin
      °b • (e′ • R′⁻ • e′)        ≈⟨ back _ tail-form ⟩
      °b • (ĥ • d′ • ĥ • d′)      ≈⟨ comm-abab °b-ĥ °b-d′ ⟩
      (ĥ • d′ • ĥ • d′) • °b      ≈⟨ front _ (sym tail-form) ⟩
      (e′ • R′⁻ • e′) • °b ∎

    °b-G : °b • ΛH₂′ ≈ ΛH₂′ • °b
    °b-G = begin
      °b • ΛH₂′                     ≈⟨ back _ ΛH₂′-rot′ ⟩
      °b • (R′ • e′ • R′⁻ • e′)     ≈⟨ comm-• (comm-abab °b-d′ °b-h₃) °b-tail ⟩
      (R′ • e′ • R′⁻ • e′) • °b     ≈⟨ front _ (sym ΛH₂′-rot′) ⟩
      ΛH₂′ • °b ∎

    -- Hence the negated CCZX and CCXZ.
    N₂-a : N₂.⟪ a ⟫ ≈ a
    N₂-a = N₂.⟪⟫-fix (sym (L-comm CH X))

    °W-form : °CCZX ≈ a • °b • a • °b
    °W-form = N₂.⟪⟫-•₄ N₂-a refl N₂-a refl

    G-°W : ΛH₂′ • °CCZX ≈ °CCZX • ΛH₂′
    G-°W = begin
      ΛH₂′ • °CCZX               ≈⟨ back _ °W-form ⟩
      ΛH₂′ • (a • °b • a • °b)   ≈⟨ comm-abab (sym a-G) (sym °b-G) ⟩
      (a • °b • a • °b) • ΛH₂′   ≈⟨ front _ (sym °W-form) ⟩
      °CCZX • ΛH₂′ ∎

    °W°V : °CCZX • °CCXZ ≈ ε
    °W°V = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)

    °V°W : °CCXZ • °CCZX ≈ ε
    °V°W = trans (sym (N₂.⟪⟫-• CCXZ CCZX)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)

    G-°V : ΛH₂′ • °CCXZ ≈ °CCXZ • ΛH₂′
    G-°V = comm-inv °W°V °V°W G-°W

    -- (177), negated on wire 2.
    °box-form : °box₃ ≈ °CCZX • S₀₁.⟪ °box₃ ⟫ • °CCXZ • S₀₁.⟪ °box₃ ⟫
    °box-form = trans (N₂.⟪⟫-cong eq177) (N₂.⟪⟫-•₄ refl N₂-box₃′ refl N₂-box₃′)

  -- (190)
  eq190 : (₄₊ n) ⊢ ΛH₂′ • °box₃ ≈ °box₃ • ΛH₂′
  eq190 = begin
    ΛH₂′ • °box₃
      ≈⟨ back _ °box-form ⟩
    ΛH₂′ • (°CCZX • S₀₁.⟪ °box₃ ⟫ • °CCXZ • S₀₁.⟪ °box₃ ⟫)
      ≈⟨ comm-• G-°W (comm-• (sym eq181ᵇ) (comm-• G-°V (sym eq181ᵇ))) ⟩
    (°CCZX • S₀₁.⟪ °box₃ ⟫ • °CCXZ • S₀₁.⟪ °box₃ ⟫) • ΛH₂′
      ≈⟨ front _ (sym °box-form) ⟩
    °box₃ • ΛH₂′ ∎

  -- The two commutations of the H gate that the colour arguments rest
  -- on, for later use.  It passes the CZ from wire 2 to its H wire,
  -- negated on wire 2 …
  °CZ₂₀-ΛH₂′ : (₄₊ n) ⊢ °CZ₂₀ • ΛH₂′ ≈ ΛH₂′ • °CZ₂₀
  °CZ₂₀-ΛH₂′ = °b-G

  -- … and the CZ from wire 2 to its box wire, negated on wire 2: that
  -- one factor by factor.
  CZ°₂₃-ΛH₂′ : (₄₊ n) ⊢ P₂₃ CZ° • ΛH₂′ ≈ ΛH₂′ • P₂₃ CZ°
  CZ°₂₃-ΛH₂′ = begin
    w • ΛH₂′                      ≈⟨ back _ ΛH₂′-rot′ ⟩
    w • (R′ • e′ • R′⁻ • e′)      ≈⟨ comm-• (comm-abab w-d′ w-h₃)
                                       (comm-• w-e′ (comm-• (comm-abab w-h₃ w-d′) w-e′)) ⟩
    (R′ • e′ • R′⁻ • e′) • w      ≈⟨ front _ (sym ΛH₂′-rot′) ⟩
    ΛH₂′ • w ∎
    where
    w : Circuit (₄₊ n)
    w = P₂₃ CZ°

    w-d′ : w • d′ ≈ d′ • w
    w-d′ = comm-23-13 CZ° CZ (evaluated Eq.refl)

    w-h₃ : w • h₃ ≈ h₃ • w
    w-h₃ = lemma-cong↑ (U (CZ° • HC)) (U (HC • CZ°)) (U-sem (CZ° • HC) (HC • CZ°) Eq.refl)

    w-e′ : w • e′ ≈ e′ • w
    w-e′ = comm-23-03 CZ° CH (evaluated Eq.refl)
