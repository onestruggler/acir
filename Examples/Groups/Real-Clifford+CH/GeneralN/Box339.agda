------------------------------------------------------------------------
-- Presentations of groups
--
-- The box against the H gate one of whose controls is the box's box
-- wire, of different colourings (Clément, Lemma D.13, Equation (339))
--
-- At the canonical position C339 (Col): the box on wire 0, black on the
-- wires 1 2, coloured a on wire 3 and x above, against the H gate on
-- wire 3 whose box wire is wire 1, black on wire 0, white on wire 2 and
-- coloured y above — the paper's reduced (339) under the swap of the
-- wires 2 3, so that the separating wire is wire 2 and the (320) of
-- GeneralN.Gadget322, whose smaller box is placed around wire 3, serves
-- both gates.  As in the paper there is no induction: both gates are
-- expanded by (320) — the H gate as the box on wire 1 between P ⊗ P on
-- the wires 1 3 — and every letter of one passes every letter of the
-- other:
--
--   * two rotations: decided on four wires (Base339) and weakened;
--   * a rotation of the box against the smaller box of the H gate, which
--     P ⊗ P on the wires 1 3 passes — its box wire and an idle wire,
--     (276) under the cycle of the placement (`P₀₃-place`, `P₁₃-S`):
--     (318) or (319) (GeneralN.Box320, Gadget319), the colours of the
--     wires above 3 being a conjugation the rotation does not see, and X
--     on wire 3 one the smaller box does not;
--   * the smaller box of the box against a rotation of the H gate: X on
--     wire 2 exchanges the colours there, P ⊗ P on the wires 1 3 is P ⊗ P
--     on the wires 0 3 — which passes the smaller box, (276) again —
--     times P ⊗ P on the wires 0 1 ((130), decided, Base339K), and what
--     is left is (322) (GeneralN.Gadget322);
--   * the two smaller boxes: (336) one width down (BoxComm), in two
--     colourings.
--
-- The smaller boxes do not see wire 3, which carries the box's one
-- colour the paper cannot move: it is the other gate's H wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box339
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem ; Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111 ; eq112)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (N₃ᵇ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (Aᴾ ; module Aj)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-cong ; low-comm ; cyc ; cyc⁻¹ ; cyc-cyc⁻¹ ; cyc⁻¹-cyc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; X-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (box276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃
  using (col ; module Col ; col-place ; col-Ex ; peel ; colT ; colT-local ; colT-pass ;
         conj-swap ; N₂-colT ; N₂-S₀₁ ; N₃ᵇ-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; P₀₃ ; P₁₃ ; Hg₃ ; C336 ; C339)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base339 using (d339 ; d339r ; G1r ; G2r)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base339K using (dK ; dK′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (module Base ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxAnywhere complete₂ complete₃ using (col-pair′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget319 complete₂ complete₃ using (bx ; eq319)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box320 complete₂ complete₃ using (eq318)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget322 complete₂ complete₃
  using (L ; zx ; xz ; kb ; kb′ ; bb ; lt ; es ; word ; via ; conj-pass ; module CW ;
         E320 ; lv ; Vb-word ; Gd ; gd ; S-place ; col-inv ; ZX-XZ ; XZ-ZX ; K-K′ ; K′-K)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (all-pairs ; module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (N₂-place ; X₂²)

------------------------------------------------------------------------
-- P ⊗ P on the wires 0 3 and 1 3

module _ {r : ℕ} where
  open Tools ((₄₊ r) VRel,_===_)

  private
    -- Conjugation by the cycle is multiplicative.
    cy : ∀ (u v : Circuit (₄₊ r)) →
         (cyc⁻¹ 3 • u • cyc 3) • (cyc⁻¹ 3 • v • cyc 3) ≈ cyc⁻¹ 3 • (u • v) • cyc 3
    cy u v = begin
      (cyc⁻¹ 3 • u • cyc 3) • (cyc⁻¹ 3 • v • cyc 3)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      cyc⁻¹ 3 • u • (cyc 3 • cyc⁻¹ 3) • v • cyc 3
        ≈⟨ back _ (back _ (trans (front _ (cyc-cyc⁻¹ {r} 3)) left-unit)) ⟩
      cyc⁻¹ 3 • u • v • cyc 3
        ≈⟨ back _ (sym assoc) ⟩
      cyc⁻¹ 3 • (u • v) • cyc 3 ∎

  P₀₃² : P₀₃ {r} • P₀₃ ≈ ε
  P₀₃² = trans (cy (PP ↓) (PP ↓)) (trans (back _ (front _ eq111)) (trans (back _ left-unit) (cyc⁻¹-cyc {r} 3)))

  P₁₃² : P₁₃ {r} • P₁₃ ≈ ε
  P₁₃² = S₀₁.⟪⟫-invol P₀₃²

  -- P ⊗ P on the wires 0 3 passes a circuit placed around wire 3 when
  -- P ⊗ P on the wires 0 1 passes it one wire up.
  P₀₃-place : ∀ (w : Circuit (₃₊ r)) → PP ↓ • w ↑ • PP ↓ ≈ w ↑ → P₀₃ • place 3 w • P₀₃ ≈ place 3 w
  P₀₃-place w e = begin
    P₀₃ • place 3 w • P₀₃                          ≈⟨ back _ (cy (w ↑) (PP ↓)) ⟩
    P₀₃ • (cyc⁻¹ 3 • (w ↑ • PP ↓) • cyc 3)         ≈⟨ cy (PP ↓) (w ↑ • PP ↓) ⟩
    cyc⁻¹ 3 • (PP ↓ • w ↑ • PP ↓) • cyc 3          ≈⟨ back _ (front _ e) ⟩
    place 3 w ∎

  -- P ⊗ P on the wires 1 3 passes the conjugate by the swap of the wires
  -- 0 1 of what P ⊗ P on the wires 0 3 passes.
  P₁₃-S : ∀ {Y : Circuit (₄₊ r)} → P₀₃ • Y • P₀₃ ≈ Y → P₁₃ • S₀₁.⟪ Y ⟫ • P₁₃ ≈ S₀₁.⟪ Y ⟫
  P₁₃-S {Y} e = trans (sym (S₀₁.⟪⟫-•₃ {a = P₀₃} {b = Y} {d = P₀₃} refl refl refl)) (S₀₁.⟪⟫-cong e)

  -- An involution passes what it fixes by conjugation.
  fix-comm : ∀ {c y : Circuit (₄₊ r)} → c • c ≈ ε → c • y • c ≈ y → c • y ≈ y • c
  fix-comm {c} {y} c² e = begin
    c • y                  ≈⟨ sym right-unit ⟩
    (c • y) • ε            ≈⟨ back _ (sym c²) ⟩
    (c • y) • (c • c)      ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (c • y • c) • c        ≈⟨ front _ e ⟩
    y • c ∎

-- (130) on the wires 0 1 3.
module _ (c₄ : Comp 4) {r : ℕ} where
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)

  klein : (₄₊ r) ⊢ P₁₃ ≈ P₀₃ • PP ↓
  klein = by-sem (P₁₃ {0}) (P₀₃ • PP ↓) (Evaluated.same dK) {r}

  klein′ : (₄₊ r) ⊢ P₁₃ ≈ PP ↓ • P₀₃
  klein′ = by-sem (P₁₃ {0}) (PP ↓ • P₀₃) (Evaluated.same dK′) {r}

------------------------------------------------------------------------
-- Colours

module _ {r : ℕ} where
  open Tools ((₃₊ r) VRel,_===_)

  -- X on wire 2 exchanges the colours there.
  flip₂ : ∀ (x : Bits r) (w : Circuit (₃₊ r)) →
          N₂.⟪ col (true ∷ true ∷ false ∷ x) w ⟫ ≈ col (true ∷ true ∷ true ∷ x) w
  flip₂ x w = begin
    X ↑ ↑ • ((X ↑ ↑ • M) • w • (X ↑ ↑ • M)) • X ↑ ↑
      ≈⟨ back _ (front _ (back _ (back _ XM))) ⟩
    X ↑ ↑ • ((X ↑ ↑ • M) • w • (M • X ↑ ↑)) • X ↑ ↑
      ≈⟨ by-passoc (□ • ((□ • □) • □ • (□ • □)) • □) (((□ • □) • (□ • □ • □)) • (□ • □)) Eq.refl ⟩
    ((X ↑ ↑ • X ↑ ↑) • (M • w • M)) • (X ↑ ↑ • X ↑ ↑)
      ≈⟨ trans (back _ XX) (trans right-unit (trans (front _ XX) left-unit)) ⟩
    M • w • M ∎
    where
    M : Circuit (₃₊ r)
    M = negsB x ↑ ↑ ↑
    XM : X ↑ ↑ • M ≈ M • X ↑ ↑
    XM = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (negsB x)))
    XX : X ↑ ↑ • X ↑ ↑ ≈ ε
    XX = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

------------------------------------------------------------------------
-- The rotation pairs, decided on four wires and weakened

-- The triply controlled ZX on wire 0 (true) or 1 (false); and the H
-- gate's, conjugated by the swap of the wires 0 1 and by P ⊗ P on the
-- wires 1 3.
U₁ U₂ : Bool → Circuit 4
U₁ true  = ΛZX 3
U₁ false = Ex • ΛZX 3 • Ex
U₂ true  = P₁₃ • (Ex • ΛZX 3 • Ex) • P₁₃
U₂ false = P₁₃ • (Ex • (Ex • ΛZX 3 • Ex) • Ex) • P₁₃

module _ (c₄ : Comp 4) {n : ℕ} where
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)

  rr : ∀ a b c → (₄₊ n) ⊢ N₃ᵇ a (U₁ b ↓ᵏ n) • N₂.⟪ U₂ c ↓ᵏ n ⟫ ≈ N₂.⟪ U₂ c ↓ᵏ n ⟫ • N₃ᵇ a (U₁ b ↓ᵏ n)
  rr true  true  true  = by-sem (G1r true  true  • G2r true ) (G2r true  • G1r true  true ) (Evaluated.same (d339r true  true  true )) {n}
  rr true  true  false = by-sem (G1r true  true  • G2r false) (G2r false • G1r true  true ) (Evaluated.same (d339r true  true  false)) {n}
  rr true  false true  = by-sem (G1r true  false • G2r true ) (G2r true  • G1r true  false) (Evaluated.same (d339r true  false true )) {n}
  rr true  false false = by-sem (G1r true  false • G2r false) (G2r false • G1r true  false) (Evaluated.same (d339r true  false false)) {n}
  rr false true  true  = by-sem (G1r false true  • G2r true ) (G2r true  • G1r false true ) (Evaluated.same (d339r false true  true )) {n}
  rr false true  false = by-sem (G1r false true  • G2r false) (G2r false • G1r false true ) (Evaluated.same (d339r false true  false)) {n}
  rr false false true  = by-sem (G1r false false • G2r true ) (G2r true  • G1r false false) (Evaluated.same (d339r false false true )) {n}
  rr false false false = by-sem (G1r false false • G2r false) (G2r false • G1r false false) (Evaluated.same (d339r false false false)) {n}

------------------------------------------------------------------------
-- (336) one width down

c336 : ∀ k → Below (₁₊ (₄₊ k)) → C336 (₁₊ k)
c336 zero    b = Base.c336₁ (b (n<1+n 4))
c336 (suc k) b = eq336ᶜ k (below-suc b)

------------------------------------------------------------------------
-- At width 5 + k

module Step (k : ℕ) (below : Below (₁₊ (₄₊ k))) (a : Bool) (x y : Bits (₁₊ k)) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

  Λ : Circuit N
  Λ = Λ□ (₄₊ k)

  s₁ s₂ : Bits N
  s₁ = true ∷ true ∷ true ∷ a ∷ x
  s₂ = true ∷ true ∷ false ∷ true ∷ y

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)

  private
    Λ′ B₁′ : Circuit (₄₊ k)
    Λ′  = Λ□ (₃₊ k)
    B₁′ = B₁ (₁₊ k)

    module C₁ = Carry {N} (Ex ↓) Ex²
    module C₂ = Carry {N} (X ↑ ↑) X₂²
    module Cs₁ = Col s₁
    module Cs₂ = Col s₂
    module Pc = Conj {N} P₁₃ P₁₃²

    -- The letters.
    F₂ : Circuit N → Circuit N
    F₂ w = col s₂ (P₁₃ • S₀₁.⟪ w ⟫ • P₁₃)

    f₁ f₂ : L → Circuit N
    f₁ l = col s₁ (lt (suc k) l)
    f₂ l = F₂ (lt (suc k) l)

    G₁-word : col s₁ Λ ≈ word f₁ es
    G₁-word = trans (Cs₁.⟪⟫-cong (E320 c₄ (suc k) below)) (CW.⟪⟫-word (negsB s₁) (negs² s₁) (lt (suc k)) es)

    G₂-word : col s₂ (Hg₃ (₁₊ k)) ≈ word f₂ es
    G₂-word = trans (Cs₂.⟪⟫-cong (trans (mid _ _ (Vb-word c₄ (suc k) below false))
                                         (CW.⟪⟫-word P₁₃ P₁₃² (lv (suc k) false) es)))
                    (CW.⟪⟫-word (negsB s₂) (negs² s₂) (λ l → P₁₃ • S₀₁.⟪ lt (suc k) l ⟫ • P₁₃) es)

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p′ • q′ ≈ q′ • p′ → p • q ≈ q • p
    both ep eq e = trans (cong ep eq) (trans e (sym (cong eq ep)))

    --------------------------------------------------------------------
    -- The rotations are local

    n₁ : ∀ (u : Circuit 4) → col s₁ (u ↓ᵏ suc k) ≈ N₃ᵇ a (u ↓ᵏ suc k)
    n₁ u = trans (peel true true true a x (u ↓ᵏ suc k)) (N₃ᵇ-cong a (colT-local u x))

    n₂ : ∀ (u : Circuit 4) → col s₂ (u ↓ᵏ suc k) ≈ N₂.⟪ u ↓ᵏ suc k ⟫
    n₂ u = trans (peel true true false true y (u ↓ᵏ suc k)) (N₂.⟪⟫-cong (colT-local u y))

    --------------------------------------------------------------------
    -- The smaller boxes

    t₁ t₂ tg : Bits (₄₊ k)
    t₁ = true ∷ true ∷ true ∷ x
    t₂ = true ∷ true ∷ false ∷ y
    tg = true ∷ true ∷ false ∷ x

    Q₁ Q₂ Qg Qg′ : Circuit N
    Q₁  = place 3 (col t₁ Λ′)
    Q₂  = place 3 (col t₂ B₁′)
    Qg  = place 3 (col tg Λ′)
    Qg′ = place 3 (col tg B₁′)

    f₁-bb : f₁ bb ≈ Q₁
    f₁-bb = col-place true true true a x Λ′

    f₂-bb : f₂ bb ≈ Q₂
    f₂-bb = begin
      col s₂ (P₁₃ • S₀₁.⟪ place 3 Λ′ ⟫ • P₁₃)
        ≈⟨ Cs₂.⟪⟫-cong (P₁₃-S (P₀₃-place Λ′ (box276 (suc k) c))) ⟩
      col s₂ (S₀₁.⟪ place 3 Λ′ ⟫)
        ≈⟨ Cs₂.⟪⟫-cong (S-place Λ′) ⟩
      col s₂ (place 3 B₁′)
        ≈⟨ col-place true true false true y B₁′ ⟩
      Q₂ ∎

    --------------------------------------------------------------------
    -- A rotation of the box against the smaller box of the H gate

    X₃² : X ↑ ↑ ↑ • X ↑ ↑ ↑ ≈ ε
    X₃² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ X²))

    X₃-Q₂ : X ↑ ↑ ↑ • Q₂ ≈ Q₂ • X ↑ ↑ ↑
    X₃-Q₂ = X-place 3 (col t₂ B₁′)

    -- X on wire 3, which the smaller box does not see.
    n3-pass : ∀ a′ {R : Circuit N} → R • Q₂ ≈ Q₂ • R → N₃ᵇ a′ R • Q₂ ≈ Q₂ • N₃ᵇ a′ R
    n3-pass true  e = e
    n3-pass false e = sym (conj-pass X₃² X₃-Q₂ (sym e))

    -- The smaller box of the H gate is the box of (318) and (319) under
    -- the swap of the wires 0 1, coloured above wire 3.
    Q₂-T : Q₂ ≈ colT y (S₀₁.⟪ bx k true false ⟫)
    Q₂-T = begin
      place 3 (col t₂ B₁′)
        ≈⟨ sym (col-place true true false true y B₁′) ⟩
      col s₂ (place 3 B₁′)
        ≈⟨ peel true true false true y (place 3 B₁′) ⟩
      N₂.⟪ colT y (place 3 B₁′) ⟫
        ≈⟨ N₂-colT false y (place 3 B₁′) ⟩
      colT y (N₂.⟪ place 3 B₁′ ⟫)
        ≈⟨ back _ (front _ (trans (N₂.⟪⟫-cong (sym (S-place Λ′))) (N₂-S₀₁ false (place 3 Λ′)))) ⟩
      colT y (S₀₁.⟪ N₂.⟪ place 3 Λ′ ⟫ ⟫) ∎

    r-Q₂ : ∀ (u : Circuit 4) → S₀₁.⟪ u ↓ᵏ suc k ⟫ • bx k true false ≈ bx k true false • S₀₁.⟪ u ↓ᵏ suc k ⟫ →
           (u ↓ᵏ suc k) • Q₂ ≈ Q₂ • (u ↓ᵏ suc k)
    r-Q₂ u e = via Q₂-T (colT-pass u y (C₁.carry (S₀₁.⟪⟫-⟪⟫ (u ↓ᵏ suc k)) refl e))

    e318 : S₀₁.⟪ ZX₃ ⟫ • bx k true false ≈ bx k true false • S₀₁.⟪ ZX₃ ⟫
    e318 = eq318 k below true true

    e319 : S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ • bx k true false ≈ bx k true false • S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫
    e319 = trans (front _ (S₀₁.⟪⟫-⟪⟫ ZX₃)) (trans (eq319 k below true false) (back _ (sym (S₀₁.⟪⟫-⟪⟫ ZX₃))))

    zx-bb : f₁ zx • f₂ bb ≈ f₂ bb • f₁ zx
    zx-bb = both (n₁ (U₁ true)) f₂-bb (n3-pass a (r-Q₂ (U₁ true) e318))

    kb-bb : f₁ kb • f₂ bb ≈ f₂ bb • f₁ kb
    kb-bb = both (n₁ (U₁ false)) f₂-bb (n3-pass a (r-Q₂ (U₁ false) e319))

    --------------------------------------------------------------------
    -- The smaller box of the box against a rotation of the H gate

    -- P ⊗ P on the wires 0 1 passes a box one wire up whose colouring is
    -- black on its box wire.
    PP-col : ∀ (r′ : Bits (₃₊ k)) → PP ↓ • (col (true ∷ r′) Λ′) ↑ • PP ↓ ≈ (col (true ∷ r′) Λ′) ↑
    PP-col r′ = trans (conj-swap (low-comm PP (negsB r′)) (Λ′ ↑)) (back _ (front _ (box276 (suc k) c)))

    P₀₃-Qg : P₀₃ • Qg ≈ Qg • P₀₃
    P₀₃-Qg = fix-comm P₀₃² (P₀₃-place (col tg Λ′) (PP-col (true ∷ false ∷ x)))

    gd′ : Gd (suc k)
    gd′ = gd c₄ (suc k) below

    -- The swap of the wires 0 1 exchanges the two boxes of (322).
    S-Qg′ : S₀₁.⟪ Qg′ ⟫ ≈ Qg
    S-Qg′ = begin
      S₀₁.⟪ place 3 (col tg B₁′) ⟫            ≈⟨ S-place (col tg B₁′) ⟩
      place 3 (S₀₁.⟪ col tg B₁′ ⟫)            ≈⟨ place-cong 3 (col-Ex tg B₁′) ⟩
      place 3 (col tg (S₀₁.⟪ B₁′ ⟫))          ≈⟨ place-cong 3 (Col.⟪⟫-cong tg (S₀₁.⟪⟫-⟪⟫ Λ′)) ⟩
      Qg ∎

    -- (322) between P ⊗ P on the wires 0 3.
    Qg-P : ∀ {T : Circuit N} → Qg • Aj.⟪ T ⟫ ≈ Aj.⟪ T ⟫ • Qg → Qg • (P₁₃ • T • P₁₃) ≈ (P₁₃ • T • P₁₃) • Qg
    Qg-P {T} e = via split (conj-pass P₀₃² P₀₃-Qg e)
      where
      split : P₁₃ • T • P₁₃ ≈ P₀₃ • Aj.⟪ T ⟫ • P₀₃
      split = trans (cong (klein c₄) (back _ (klein′ c₄)))
                    (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

    Qg-zx : Qg • Aj.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ≈ Aj.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ • Qg
    Qg-zx = via (sym (conj-swap (sym eq112) ZX₃))
                (C₁.carry S-Qg′ refl (sym (gd′ true true true true x false)))

    Qg-kb : Qg • Aj.⟪ S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ⟫ ≈ Aj.⟪ S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ⟫ • Qg
    Qg-kb = via (Aj.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ ZX₃)) (sym (gd′ true true true true x true))

    -- X on wire 2 exchanges the colours there.
    N₂-Qg : N₂.⟪ Qg ⟫ ≈ Q₁
    N₂-Qg = trans (N₂-place (col tg Λ′)) (place-cong 3 (flip₂ x Λ′))

    bb-zx : f₁ bb • f₂ zx ≈ f₂ zx • f₁ bb
    bb-zx = both f₁-bb (n₂ (U₂ true)) (C₂.carry N₂-Qg refl (Qg-P Qg-zx))

    bb-kb : f₁ bb • f₂ kb ≈ f₂ kb • f₁ bb
    bb-kb = both f₁-bb (n₂ (U₂ false)) (C₂.carry N₂-Qg refl (Qg-P Qg-kb))

    --------------------------------------------------------------------
    -- The two smaller boxes: (336) one width down

    bb-bb : f₁ bb • f₂ bb ≈ f₂ bb • f₁ bb
    bb-bb = both f₁-bb f₂-bb (begin
      place 3 (col t₁ Λ′) • place 3 (col t₂ B₁′)     ≈⟨ sym (place-• 3 _ _) ⟩
      place 3 (col t₁ Λ′ • col t₂ B₁′)               ≈⟨ place-cong 3 (col-pair′ t₁ t₂ Λ′ B₁′ (c336 k below)) ⟩
      place 3 (col t₂ B₁′ • col t₁ Λ′)               ≈⟨ place-• 3 _ _ ⟩
      place 3 (col t₂ B₁′) • place 3 (col t₁ Λ′) ∎)

    --------------------------------------------------------------------
    -- Inverses

    inv₂ : ∀ {u v : Circuit N} → u • v ≈ ε → F₂ u • F₂ v ≈ ε
    inv₂ {u} {v} e = col-inv s₂ (trans (sym (Pc.⟪⟫-• (S₀₁.⟪ u ⟫) (S₀₁.⟪ v ⟫))) (trans (Pc.⟪⟫-cong
                       (trans (sym (S₀₁.⟪⟫-• u v)) (trans (S₀₁.⟪⟫-cong e) S₀₁.⟪⟫-ε))) Pc.⟪⟫-ε))

    right : ∀ {Y u v} → u • v ≈ ε → v • u ≈ ε → Y • F₂ u ≈ F₂ u • Y → Y • F₂ v ≈ F₂ v • Y
    right uv vu e = comm-inv (inv₂ uv) (inv₂ vu) e

    left : ∀ {Y w v} → w • v ≈ ε → v • w ≈ ε → w • Y ≈ Y • w → v • Y ≈ Y • v
    left wv vw e = sym (comm-inv wv vw (sym e))

    inv₁ : ∀ {w v : Circuit N} → w • v ≈ ε → col s₁ w • col s₁ v ≈ ε
    inv₁ e = col-inv s₁ e

    --------------------------------------------------------------------
    -- Every pair

    rZ : ∀ l′ → f₁ zx • f₂ l′ ≈ f₂ l′ • f₁ zx
    rZ zx  = both (n₁ (U₁ true)) (n₂ (U₂ true))  (rr c₄ a true true)
    rZ kb  = both (n₁ (U₁ true)) (n₂ (U₂ false)) (rr c₄ a true false)
    rZ xz  = right ZX-XZ XZ-ZX (rZ zx)
    rZ kb′ = right K-K′ K′-K (rZ kb)
    rZ bb  = zx-bb

    rK : ∀ l′ → f₁ kb • f₂ l′ ≈ f₂ l′ • f₁ kb
    rK zx  = both (n₁ (U₁ false)) (n₂ (U₂ true))  (rr c₄ a false true)
    rK kb  = both (n₁ (U₁ false)) (n₂ (U₂ false)) (rr c₄ a false false)
    rK xz  = right ZX-XZ XZ-ZX (rK zx)
    rK kb′ = right K-K′ K′-K (rK kb)
    rK bb  = kb-bb

    rB : ∀ l′ → f₁ bb • f₂ l′ ≈ f₂ l′ • f₁ bb
    rB zx  = bb-zx
    rB kb  = bb-kb
    rB xz  = right ZX-XZ XZ-ZX bb-zx
    rB kb′ = right K-K′ K′-K bb-kb
    rB bb  = bb-bb

    pair : ∀ l l′ → f₁ l • f₂ l′ ≈ f₂ l′ • f₁ l
    pair zx  l′ = rZ l′
    pair kb  l′ = rK l′
    pair xz  l′ = left (inv₁ ZX-XZ) (inv₁ XZ-ZX) (rZ l′)
    pair kb′ l′ = left (inv₁ K-K′) (inv₁ K′-K) (rK l′)
    pair bb  l′ = rB l′

  main : col s₁ Λ • col s₂ (Hg₃ (₁₊ k)) ≈ col s₂ (Hg₃ (₁₊ k)) • col s₁ Λ
  main = begin
    col s₁ Λ • col s₂ (Hg₃ (₁₊ k))   ≈⟨ cong G₁-word G₂-word ⟩
    word f₁ es • word f₂ es          ≈⟨ all-pairs f₁ f₂ es es pair ⟩
    word f₂ es • word f₁ es          ≈⟨ sym (cong G₂-word G₁-word) ⟩
    col s₂ (Hg₃ (₁₊ k)) • col s₁ Λ ∎

------------------------------------------------------------------------
-- (339)

-- On four wires, decided.
eq339₀ : Comp 4 → C339 0
eq339₀ c₄ true  [] [] =
  c₄ (same-sem (col (true ∷ true ∷ true ∷ true ∷ []) (Λ□ 3) • col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0))
               (col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0) • col (true ∷ true ∷ true ∷ true ∷ []) (Λ□ 3))
               (Evaluated.same (d339 true)))
eq339₀ c₄ false [] [] =
  c₄ (same-sem (col (true ∷ true ∷ true ∷ false ∷ []) (Λ□ 3) • col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0))
               (col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0) • col (true ∷ true ∷ true ∷ false ∷ []) (Λ□ 3))
               (Evaluated.same (d339 false)))

-- At every width from five on.
eq339 : ∀ k → Below (₁₊ (₄₊ k)) → C339 (₁₊ k)
eq339 k b a x y = Step.main k b a x y
