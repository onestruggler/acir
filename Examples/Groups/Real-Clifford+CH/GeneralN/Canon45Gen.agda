------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical form of rule (45) of Figure 8, at any width from four
-- with its width-specific inputs given (Clément, Lemma 8.8)
--
-- At width 4 + n, with Λ the box on wire 0, A = ΛH the H gate on wire 0
-- with its box wire on wire 1 (P ⊗ P around Λ, by definition), Zc = Λ
-- negated on wire 1 and Cw the H gate on wire 0 with its box wire on
-- wire 2, white on wire 1, as the decoding spells it:
--
--   A • Zc • Cw • A • Cw ≈ Cw • A • Cw • Zc • A                 (`core45`)
--
-- which is what rule (45) decodes to once the negations common to its
-- letters are conjugated away (Lemma88.Rule45).  All five letters are
-- involutions, so it says that the word is one.  The paper's proof is
-- six pages ((311), (337), (344), (309), (310), (277), (274), (308));
-- here it is the three-qubit proof of (146) with multiple controls:
--
--   * Cw is X on wire 1 around G, the H gate HG = Col.Hg under the swap
--     of the wires 1 2 ((338)'s X-Hg, and XY.S-ΛH);
--   * Zc = Λ M with M the box on wire 1, wire 0 idle ((309)), and M
--     passes A, Λ, X on wire 1 and G ((276), (335), (338)), so it
--     cancels from both sides: what is left is T′ = A Λ Cw′ A Cw′ equal
--     to its reverse;
--   * between P ⊗ P on the wires 0 1, A and Λ exchange, and Cw′ becomes
--     Ct Mx, with Ct = G under the swap of the wires 0 1 and Mx = K XK
--     the box on wire 2 with wire 1 idle (the Klein four-group of P ⊗ P
--     on the three lower wires, `Base45`); Mx passes Λ and Ct and is an
--     involution, so it cancels too;
--   * (Ct Λ)² ≈ (A K)², both being ΛZX by (333) under the swaps, the
--     first through (353) — and then Λ A Ct Λ Ct and its reverse are
--     both Λ K A K Λ.
--
-- The inputs that depend on the width are module parameters: the box
-- facts (`canon`, the swap of the wires 1 2 on it, (335) for the
-- colourings white on wire 1 and on wire 2, (336) white on wire 2, (276)
-- for P ⊗ P on its smaller copy), the H gate HG — the box on wire 1
-- between P ⊗ P — with its own facts ((338)
-- with x = y and with the colourings differing on wire 2, X on its box
-- wire, the H gate under the lower swap) and (333) with the swap of the
-- wires 1 2 on ΛZX.  Canon45 is the instance from five wires on, and
-- Lemma88.W4.Core45 the one on four, from Lemma D.5.  Every step was
-- checked numerically at four to seven wires first (scratchpad
-- r4x/plan45.py, review-r45.py; small-widths/r4546/t45m1.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon45Gen
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  {n : ℕ}
  (canon : Canon (₁₊ n))
  (HG : Circuit (₄₊ n))
  (Hg-form : (₄₊ n) ⊢ HG ≈ PP ↓ • (Ex ↓ • Λ□ (₃₊ n) • Ex ↓) • PP ↓)
  (S-ΛH : (₄₊ n) ⊢ Ex ↓ • ΛH (₂₊ n) • Ex ↓ ≈ HG)
  (X-Hg : (₄₊ n) ⊢ X ↑ • HG ≈ HG • X ↑)
  (eq338xy : (₄₊ n) ⊢ Λ□ (₃₊ n) • HG ≈ HG • Λ□ (₃₊ n))
  (S₁₂-Λ : (₄₊ n) ⊢ Ex ↑ • Λ□ (₃₊ n) • Ex ↑ ≈ Λ□ (₃₊ n))
  (Λ-Zc : (₄₊ n) ⊢ Λ□ (₃₊ n) • (X ↑ • Λ□ (₃₊ n) • X ↑) ≈ (X ↑ • Λ□ (₃₊ n) • X ↑) • Λ□ (₃₊ n))
  (PP-M : (₄₊ n) ⊢ PP ↓ • Λ□ (₂₊ n) ↑ ≈ Λ□ (₂₊ n) ↑ • PP ↓)
  (sepΛ : (₄₊ n) ⊢ Λ□ (₃₊ n) • (X ↑ ↑ • HG • X ↑ ↑) ≈ (X ↑ ↑ • HG • X ↑ ↑) • Λ□ (₃₊ n))
  (c336′ : (₄₊ n) ⊢ Λ□ (₃₊ n) • (X ↑ ↑ • (Ex ↓ • Λ□ (₃₊ n) • Ex ↓) • X ↑ ↑)
                   ≈ (X ↑ ↑ • (Ex ↓ • Λ□ (₃₊ n) • Ex ↓) • X ↑ ↑) • Λ□ (₃₊ n))
  (c335′ : (₄₊ n) ⊢ Λ□ (₃₊ n) • (X ↑ ↑ • Λ□ (₃₊ n) • X ↑ ↑) ≈ (X ↑ ↑ • Λ□ (₃₊ n) • X ↑ ↑) • Λ□ (₃₊ n))
  (eq333 : (₄₊ n) ⊢ HG • (Ex ↑ • (Ex ↓ • Λ□ (₃₊ n) • Ex ↓) • Ex ↑) • HG • (Ex ↑ • (Ex ↓ • Λ□ (₃₊ n) • Ex ↓) • Ex ↑)
                   ≈ ΛZX (₃₊ n))
  (S-ZX : (₄₊ n) ⊢ Ex ↑ • ΛZX (₃₊ n) • Ex ↑ ≈ ΛZX (₃₊ n))
  where

open import Data.Nat using (s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁ ; module S₁₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swap-braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base45 using (e-PP₁ ; e-PP₂ ; e-PP₃ ; e-τP ; e-τX₁)

module _ where

  private
    N : ℕ
    N = ₄₊ n

  open Tools (N VRel,_===_)
  open SS.Below 3 (s≤s (s≤s (s≤s z≤n))) complete₃ using () renaming (by-sem to by-sem₃)

  Λ A Zc Cw : Circuit N
  Λ  = Λ□ (₃₊ n)
  A  = ΛH (₂₊ n)
  Zc = X ↑ • Λ • X ↑
  Cw = (X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • A • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)

  private
    B K G M Ct XK Mx P₀₂ Cw′ : Circuit N
    B   = Ex ↓ • Λ • Ex ↓
    K   = S₁₂.⟪ B ⟫
    G   = S₁₂.⟪ HG ⟫
    M   = Λ□ (₂₊ n) ↑
    Ct  = Ex ↓ • G • Ex ↓
    XK  = X ↑ • K • X ↑
    Mx  = K • XK
    P₀₂ = S₁₂.⟪ PP ↓ ⟫
    Cw′ = X ↑ • G • X ↑

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
    both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

    fixc : ∀ {s u : Circuit N} → s • u ≈ u • s → s • s ≈ ε → s • u • s ≈ u
    fixc e s² = trans (sym assoc) (trans (front _ e) (trans assoc (trans (back _ s²) right-unit)))

    --------------------------------------------------------------------
    -- Involutions and conjugations

    X↑² : X ↑ • X ↑ ≈ ε
    X↑² = lemma-cong↑ _ _ X²

    X↑↑² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    τ² : τ₀₂ • τ₀₂ ≈ ε
    τ² = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)

    module Carry (c : Circuit N) (c² : c • c ≈ ε) where
      open Conj c c²
      carry : ∀ {a b a′ b′} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → a • b ≈ b • a → a′ • b′ ≈ b′ • a′
      carry ea eb e = ⟪⟫-≈ e (⟪⟫-•₂ ea eb) (⟪⟫-•₂ eb ea)

    module C₀₁ = Carry Ex Ex²
    module C₁₂ = Carry (Ex ↑) Ex↑²
    module Cτ  = Carry τ₀₂ τ²
    module CX  = Carry (X ↑) X↑²
    module CX₂ = Carry (X ↑ ↑) X↑↑²
    module E₀  = Conj {N} Ex Ex²
    module X₁  = Conj {N} (X ↑) X↑²
    module Tτ  = Conj {N} τ₀₂ τ²
    module Pc  = Conj {N} (PP ↓) eq111

    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    A² : A • A ≈ ε
    A² = Pc.⟪⟫-invol Λ²

    K² : K • K ≈ ε
    K² = S₁₂.⟪⟫-invol (S₀₁.⟪⟫-invol Λ²)

    XK² : XK • XK ≈ ε
    XK² = X₁.⟪⟫-invol K²

    -- X on the wires 1 2 under the swaps.
    S₁₂X₁ : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
    S₁₂X₁ = X-step 1 (s≤s (s≤s z≤n))

    S₁₂X₂ : S₁₂.⟪ X ↑ ↑ ⟫ ≈ X ↑
    S₁₂X₂ = conj-sym Ex↑² S₁₂X₁

    S₀₁X₂ : S₀₁.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
    S₀₁X₂ = fixc (low-comm Ex X) Ex²

    -- The swap of the wires 0 1 on the box.
    br : Ex • Ex ↑ • Ex ≈ Ex ↑ • Ex • Ex ↑
    br = swap-braid 0 (s≤s (s≤s (s≤s z≤n)))

    τΛ : Tτ.⟪ Λ ⟫ ≈ K
    τΛ = begin
      (Ex • Ex ↑ • Ex) • Λ • (Ex • Ex ↑ • Ex)
        ≈⟨ cong br (back _ br) ⟩
      (Ex ↑ • Ex • Ex ↑) • Λ • (Ex ↑ • Ex • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      Ex ↑ • (Ex • S₁₂.⟪ Λ ⟫ • Ex) • Ex ↑
        ≈⟨ mid _ _ (mid _ _ S₁₂-Λ) ⟩
      K ∎

    ExK : E₀.⟪ K ⟫ ≈ K
    ExK = trans (by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl) τΛ

    --------------------------------------------------------------------
    -- Cw is X on wire 1 around G

    XX-sw : X ↑ • X ↑ ↑ ≈ X ↑ ↑ • X ↑
    XX-sw = lemma-cong↑ _ _ (X-↑ X)

    X₂G : X ↑ ↑ • G • X ↑ ↑ ≈ G
    X₂G = trans (sym (S₁₂.⟪⟫-•₃ S₁₂X₁ refl S₁₂X₁)) (S₁₂.⟪⟫-cong (fixc X-Hg X↑²))

    Cw-form : Cw ≈ Cw′
    Cw-form = begin
      (X ↑ • X ↑ ↑) • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • (X ↑ • X ↑ ↑)
        ≈⟨ back _ (back _ (back _ (back _ XX-sw))) ⟩
      (X ↑ • X ↑ ↑) • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • (X ↑ ↑ • X ↑)
        ≈⟨ by-passoc ((□ • □) • (□ • □) • □ • (□ • □) • (□ • □)) (□ • (□ • □ • (□ • □ • □) • □ • □) • □) Eq.refl ⟩
      X ↑ • (X ↑ ↑ • Ex ↑ • (Ex • A • Ex) • Ex ↑ • X ↑ ↑) • X ↑
        ≈⟨ mid _ _ (back _ (back _ (front _ S-ΛH))) ⟩
      X ↑ • (X ↑ ↑ • Ex ↑ • HG • Ex ↑ • X ↑ ↑) • X ↑
        ≈⟨ mid _ _ (trans (by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl) X₂G) ⟩
      Cw′ ∎

    --------------------------------------------------------------------
    -- Zc = Λ M, and M passes A, Λ and Cw′

    merge : Λ • Zc ≈ M
    merge = Canon.merge canon

    Zc-ΛM : Zc ≈ Λ • M
    Zc-ΛM = trans (sym (trans (sym assoc) (trans (front _ Λ²) left-unit))) (back _ merge)

    Λ-M : Λ • M ≈ M • Λ
    Λ-M = via (sym merge) (pass₂ refl Λ-Zc)

    M-A : M • A ≈ A • M
    M-A = pass₂ (sym PP-M) (pass₂ (sym Λ-M) (sym PP-M))

    XMX : X₁.⟪ M ⟫ ≈ M
    XMX = trans (X₁.⟪⟫-cong (sym merge))
                (trans (X₁.⟪⟫-• Λ Zc) (trans (back _ (X₁.⟪⟫-⟪⟫ Λ)) (trans (sym Λ-Zc) merge)))

    M-X : M • X ↑ ≈ X ↑ • M
    M-X = sym (X₁.⟪⟫-comm XMX)

    Λ-G : Λ • G ≈ G • Λ
    Λ-G = C₁₂.carry S₁₂-Λ refl eq338xy

    Zc-G : Zc • G ≈ G • Zc
    Zc-G = C₁₂.carry (S₁₂.⟪⟫-•₃ S₁₂X₂ S₁₂-Λ S₁₂X₂) refl (CX₂.carry refl (unconj X↑↑²) sepΛ)

    M-G : M • G ≈ G • M
    M-G = both merge refl (passL Λ-G Zc-G)

    M-Cw′ : M • Cw′ ≈ Cw′ • M
    M-Cw′ = pass₂ M-X (pass₂ M-G M-X)

    --------------------------------------------------------------------
    -- M cancels: T′ equal to its reverse suffices

    T′ R′ : Circuit N
    T′ = A • Λ • Cw′ • A • Cw′
    R′ = Cw′ • A • Cw′ • Λ • A

    lhs-red : A • Zc • Cw′ • A • Cw′ ≈ T′ • M
    lhs-red = begin
      A • Zc • Cw′ • A • Cw′
        ≈⟨ back _ (front _ Zc-ΛM) ⟩
      A • (Λ • M) • Cw′ • A • Cw′
        ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • (□ • □ • □))) Eq.refl ⟩
      A • Λ • (M • (Cw′ • A • Cw′))
        ≈⟨ back _ (back _ (pass₂ M-Cw′ (pass₂ M-A M-Cw′))) ⟩
      A • Λ • ((Cw′ • A • Cw′) • M)
        ≈⟨ by-passoc (□ • □ • ((□ • □ • □) • □)) ((□ • □ • □ • □ • □) • □) Eq.refl ⟩
      T′ • M ∎

    rhs-red : Cw′ • A • Cw′ • Zc • A ≈ R′ • M
    rhs-red = begin
      Cw′ • A • Cw′ • Zc • A
        ≈⟨ back _ (back _ (back _ (front _ Zc-ΛM))) ⟩
      Cw′ • A • Cw′ • (Λ • M) • A
        ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
      Cw′ • A • Cw′ • Λ • (M • A)
        ≈⟨ back _ (back _ (back _ (back _ M-A))) ⟩
      Cw′ • A • Cw′ • Λ • (A • M)
        ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □)) ((□ • □ • □ • □ • □) • □) Eq.refl ⟩
      R′ • M ∎

    --------------------------------------------------------------------
    -- Between P ⊗ P on the wires 0 1: Cw′ is Ct Mx

    G-P : G ≈ P₀₂ • K • P₀₂
    G-P = trans (S₁₂.⟪⟫-cong Hg-form) (S₁₂.⟪⟫-•₃ refl refl refl)

    X-P₀₂ : X ↑ • P₀₂ ≈ P₀₂ • X ↑
    X-P₀₂ = C₁₂.carry S₁₂X₂ refl (sym (low-comm PP X))

    XK-Mx : XK ≈ K • Mx
    XK-Mx = sym (trans (sym assoc) (trans (front _ K²) left-unit))

    P₀₂-P : PP ↓ • P₀₂ ≈ PP ↑
    P₀₂-P = by-sem₃ (PP ↓ • (Ex ↑ • PP ↓ • Ex ↑)) (PP ↑) (Evaluated.same e-PP₁) {₁₊ n}

    P-P₀₂ : P₀₂ • PP ↓ ≈ PP ↑
    P-P₀₂ = by-sem₃ ((Ex ↑ • PP ↓ • Ex ↑) • PP ↓) (PP ↑) (Evaluated.same e-PP₂) {₁₊ n}

    ExP : E₀.⟪ P₀₂ ⟫ ≈ PP ↑
    ExP = by-sem₃ (Ex ↓ • (Ex ↑ • PP ↓ • Ex ↑) • Ex ↓) (PP ↑) (Evaluated.same e-PP₃) {₁₊ n}

    τP : Tτ.⟪ PP ↓ ⟫ ≈ PP ↑
    τP = by-sem₃ (τ₀₂ • PP ↓ • τ₀₂) (PP ↑) (Evaluated.same e-τP) {₁₊ n}

    τX : Tτ.⟪ X ↑ ⟫ ≈ X ↑
    τX = by-sem₃ (τ₀₂ • X ↑ • τ₀₂) (X ↑) (Evaluated.same e-τX₁) {₁₊ n}

    -- Mx is the box on wire 2, wire 1 idle: M under τ₀₂.
    τM : Tτ.⟪ M ⟫ ≈ Mx
    τM = trans (Tτ.⟪⟫-cong (sym merge)) (trans (Tτ.⟪⟫-• Λ Zc) (cong τΛ (Tτ.⟪⟫-•₃ τX τΛ τX)))

    Mx-PP : Mx • PP ↑ ≈ PP ↑ • Mx
    Mx-PP = Cτ.carry τM τP (sym PP-M)

    Ct-P : Ct ≈ PP ↑ • K • PP ↑
    Ct-P = trans (E₀.⟪⟫-cong G-P) (E₀.⟪⟫-•₃ ExP ExK ExP)

    N2 : Pc.⟪ Cw′ ⟫ ≈ Ct • Mx
    N2 = begin
      PP ↓ • (X ↑ • G • X ↑) • PP ↓
        ≈⟨ mid _ _ (mid _ _ G-P) ⟩
      PP ↓ • (X ↑ • (P₀₂ • K • P₀₂) • X ↑) • PP ↓
        ≈⟨ mid _ _ (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl) ⟩
      PP ↓ • ((X ↑ • P₀₂) • K • (P₀₂ • X ↑)) • PP ↓
        ≈⟨ mid _ _ (cong X-P₀₂ (back _ (sym X-P₀₂))) ⟩
      PP ↓ • ((P₀₂ • X ↑) • K • (X ↑ • P₀₂)) • PP ↓
        ≈⟨ mid _ _ (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl) ⟩
      PP ↓ • (P₀₂ • XK • P₀₂) • PP ↓
        ≈⟨ mid _ _ (back _ (front _ XK-Mx)) ⟩
      PP ↓ • (P₀₂ • (K • Mx) • P₀₂) • PP ↓
        ≈⟨ by-passoc (□ • (□ • (□ • □) • □) • □) ((□ • □) • □ • □ • (□ • □)) Eq.refl ⟩
      (PP ↓ • P₀₂) • K • Mx • (P₀₂ • PP ↓)
        ≈⟨ cong P₀₂-P (back _ (back _ P-P₀₂)) ⟩
      PP ↑ • K • Mx • PP ↑
        ≈⟨ back _ (back _ Mx-PP) ⟩
      PP ↑ • K • PP ↑ • Mx
        ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ (sym Ct-P)) ⟩
      Ct • Mx ∎

    --------------------------------------------------------------------
    -- Mx passes Λ and Ct, and is an involution

    K-Λ : K • Λ ≈ Λ • K
    K-Λ = sym (C₁₂.carry S₁₂-Λ refl (Canon.comm336 canon))

    Zc-K : Zc • K ≈ K • Zc
    Zc-K = C₁₂.carry (S₁₂.⟪⟫-•₃ S₁₂X₂ S₁₂-Λ S₁₂X₂) refl (CX₂.carry refl (unconj X↑↑²) c336′)

    XK-Λ : XK • Λ ≈ Λ • XK
    XK-Λ = CX.carry refl (unconj X↑²) (sym Zc-K)

    Mx-Λ : Mx • Λ ≈ Λ • Mx
    Mx-Λ = passL K-Λ XK-Λ

    K-XK : K • XK ≈ XK • K
    K-XK = C₁₂.carry refl (S₁₂.⟪⟫-•₃ S₁₂X₂ refl S₁₂X₂) (C₀₁.carry refl (S₀₁.⟪⟫-•₃ S₀₁X₂ refl S₀₁X₂) c335′)

    Mx-K : Mx • K ≈ K • Mx
    Mx-K = passL refl (sym K-XK)

    Mx-Ct : Mx • Ct ≈ Ct • Mx
    Mx-Ct = via Ct-P (pass₂ Mx-PP (pass₂ Mx-K Mx-PP))

    Mx² : Mx • Mx ≈ ε
    Mx² = begin
      (K • XK) • (K • XK)      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      K • (XK • K) • XK        ≈⟨ back _ (front _ (sym K-XK)) ⟩
      K • (K • XK) • XK        ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
      (K • K) • (XK • XK)      ≈⟨ trans (cong K² XK²) left-unit ⟩
      ε ∎

    MΛC : Mx • (Λ • Ct) • Mx ≈ Λ • Ct
    MΛC = fixc (pass₂ Mx-Λ Mx-Ct) Mx²

    --------------------------------------------------------------------
    -- T′ and its reverse between P ⊗ P

    PA : Pc.⟪ A ⟫ ≈ Λ
    PA = Pc.⟪⟫-⟪⟫ Λ

    PT : Pc.⟪ T′ ⟫ ≈ Λ • A • Ct • Λ • Ct
    PT = begin
      Pc.⟪ A • Λ • Cw′ • A • Cw′ ⟫
        ≈⟨ Pc.⟪⟫-•₂ PA (Pc.⟪⟫-•₄ refl N2 PA N2) ⟩
      Λ • A • (Ct • Mx) • Λ • (Ct • Mx)
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • (□ • □)) (□ • □ • □ • (□ • (□ • □) • □)) Eq.refl ⟩
      Λ • A • Ct • (Mx • (Λ • Ct) • Mx)
        ≈⟨ back _ (back _ (back _ MΛC)) ⟩
      Λ • A • Ct • Λ • Ct ∎

    PR : Pc.⟪ R′ ⟫ ≈ Ct • Λ • Ct • A • Λ
    PR = begin
      Pc.⟪ Cw′ • A • Cw′ • Λ • A ⟫
        ≈⟨ Pc.⟪⟫-•₂ N2 (Pc.⟪⟫-•₄ PA N2 refl PA) ⟩
      (Ct • Mx) • Λ • (Ct • Mx) • A • Λ
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □ • □) (□ • (□ • (□ • □) • □) • □ • □) Eq.refl ⟩
      Ct • (Mx • (Λ • Ct) • Mx) • A • Λ
        ≈⟨ back _ (front _ MΛC) ⟩
      Ct • (Λ • Ct) • A • Λ
        ≈⟨ back _ assoc ⟩
      Ct • Λ • Ct • A • Λ ∎

    --------------------------------------------------------------------
    -- (Ct Λ)² ≈ (A K)²: both are ΛZX under the swap of the wires 0 1

    key : Ct • Λ • Ct • Λ ≈ A • K • A • K
    key = E₀.⟪⟫-≈ e (E₀.⟪⟫-⟪⟫ _) (E₀.⟪⟫-⟪⟫ _)
      where
      e : E₀.⟪ Ct • Λ • Ct • Λ ⟫ ≈ E₀.⟪ A • K • A • K ⟫
      e = begin
        E₀.⟪ Ct • Λ • Ct • Λ ⟫
          ≈⟨ E₀.⟪⟫-•₄ (E₀.⟪⟫-⟪⟫ G) refl (E₀.⟪⟫-⟪⟫ G) refl ⟩
        G • B • G • B
          ≈⟨ sym (S₁₂.⟪⟫-•₄ refl (S₁₂.⟪⟫-⟪⟫ B) refl (S₁₂.⟪⟫-⟪⟫ B)) ⟩
        S₁₂.⟪ HG • K • HG • K ⟫
          ≈⟨ S₁₂.⟪⟫-cong (eq333) ⟩
        S₁₂.⟪ ΛZX (₃₊ n) ⟫
          ≈⟨ S-ZX ⟩
        ΛZX (₃₊ n)
          ≈⟨ sym (eq333) ⟩
        HG • K • HG • K
          ≈⟨ sym (E₀.⟪⟫-•₄ S-ΛH ExK S-ΛH ExK) ⟩
        E₀.⟪ A • K • A • K ⟫ ∎

    -- The same read backwards: every letter is an involution.
    key′ : Λ • Ct • Λ • Ct ≈ K • A • K • A
    key′ = begin
      Λ • Ct • Λ • Ct
        ≈⟨ sym right-unit ⟩
      (Λ • Ct • Λ • Ct) • ε
        ≈⟨ back _ (sym (cancel4 A² K²)) ⟩
      (Λ • Ct • Λ • Ct) • ((A • K • A • K) • (K • A • K • A))
        ≈⟨ back _ (front _ (sym key)) ⟩
      (Λ • Ct • Λ • Ct) • ((Ct • Λ • Ct • Λ) • (K • A • K • A))
        ≈⟨ trans (sym assoc) (front _ (cancel4 Λ² Ct²)) ⟩
      ε • (K • A • K • A)
        ≈⟨ left-unit ⟩
      K • A • K • A ∎
      where
      Ct² : Ct • Ct ≈ ε
      Ct² = E₀.⟪⟫-invol (S₁₂.⟪⟫-invol (trans (cong Hg-form Hg-form) (Pc.⟪⟫-invol (S₀₁.⟪⟫-invol Λ²))))
      cancel4 : ∀ {a b : Circuit N} → a • a ≈ ε → b • b ≈ ε → (a • b • a • b) • (b • a • b • a) ≈ ε
      cancel4 {a} {b} a² b² = begin
        (a • b • a • b) • (b • a • b • a)
          ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
        a • b • a • (b • b) • a • b • a
          ≈⟨ back _ (back _ (back _ (trans (front _ b²) left-unit))) ⟩
        a • b • a • a • b • a
          ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ a²) left-unit))) ⟩
        a • b • b • a
          ≈⟨ back _ (trans (sym assoc) (trans (front _ b²) left-unit)) ⟩
        a • a
          ≈⟨ a² ⟩
        ε ∎

    -- Both T₂ and its reverse are Λ K A K Λ.
    palin : Λ • A • Ct • Λ • Ct ≈ Ct • Λ • Ct • A • Λ
    palin = begin
      Λ • A • Ct • Λ • Ct
        ≈⟨ back _ (back _ (sym (trans (by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl)
                                         (back _ (back _ (trans (back _ Λ²) right-unit)))))) ⟩
      Λ • A • ((Ct • Λ • Ct • Λ) • Λ)
        ≈⟨ back _ (back _ (front _ key)) ⟩
      Λ • A • ((A • K • A • K) • Λ)
        ≈⟨ back _ (trans (by-passoc (□ • ((□ • □ • □ • □) • □)) ((□ • □) • □ • □ • □ • □) Eq.refl)
                         (trans (front _ A²) left-unit)) ⟩
      Λ • K • A • K • Λ
        ≈⟨ back _ (sym (trans (by-passoc ((□ • □ • □ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl)
                              (back _ (back _ (back _ (trans (front _ A²) left-unit)))))) ⟩
      Λ • (K • A • K • A) • A • Λ
        ≈⟨ back _ (front _ (sym key′)) ⟩
      Λ • (Λ • Ct • Λ • Ct) • A • Λ
        ≈⟨ trans (by-passoc (□ • (□ • □ • □ • □) • □ • □) ((□ • □) • □ • □ • □ • □ • □) Eq.refl)
                 (trans (front _ Λ²) left-unit) ⟩
      Ct • Λ • Ct • A • Λ ∎

    T′-R′ : T′ ≈ R′
    T′-R′ = Pc.⟪⟫-≈ palin (trans (Pc.⟪⟫-cong (sym PT)) (Pc.⟪⟫-⟪⟫ T′)) (trans (Pc.⟪⟫-cong (sym PR)) (Pc.⟪⟫-⟪⟫ R′))

  ------------------------------------------------------------------------
  -- Rule (45), canonical

  core45 : A • Zc • Cw • A • Cw ≈ Cw • A • Cw • Zc • A
  core45 = begin
    A • Zc • Cw • A • Cw
      ≈⟨ back _ (back _ (cong Cw-form (back _ Cw-form))) ⟩
    A • Zc • Cw′ • A • Cw′
      ≈⟨ lhs-red ⟩
    T′ • M
      ≈⟨ front _ T′-R′ ⟩
    R′ • M
      ≈⟨ sym rhs-red ⟩
    Cw′ • A • Cw′ • Zc • A
      ≈⟨ sym (cong Cw-form (back _ (cong Cw-form refl))) ⟩
    Cw • A • Cw • Zc • A ∎
