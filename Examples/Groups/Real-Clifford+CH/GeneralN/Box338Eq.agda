------------------------------------------------------------------------
-- Presentations of groups
--
-- The box against the H gate whose box wire is a control of the box, all
-- controls black (Clément, Lemma D.13, Equation (338), x = y)
--
-- At width 5 + k: the box Λ on wire 0 commutes with the H gate Hg on
-- wire 0 whose box wire is wire 1 (Col), all their other controls
-- black.  The paper derives it from the 2ⁿ − 1 cases x ≠ y and a merge
-- of the boxes over every colouring.  Here it is the argument of
-- BoxForms' (336) between P ⊗ P, as proposed by the analysis of the
-- decoding of rule (39): with R = P ⊗ P on the wires 0 1, B the box B□
-- on wire 1 with wire 2 idle and E = R B R,
--
--   * R Λ R = (R W R) B (R V R) B, the E-form (284) (Keystone);
--   * B₁₀ = B D = D B, D the box B₁₀ on wire 1 negated on wire 2, by the
--     merges (301), (302) under the swap of the wires 0 1;
--   * D passes B, and R W R and R V R (`g292`, below);
--   * B (R W R) B (R V R) = R (E W E V) R = R Λ R, the E-form rotated:
--     Λ is an involution (299) and W, V are inverse.
--
-- So R Λ R • B₁₀ = (R W R) B (R V R) D = D (R W R) B (R V R)
-- = B₁₀ B (R W R) B (R V R) = B₁₀ • R Λ R, and conjugating by R gives
-- (338).
--
-- `g292`: CCZX between P ⊗ P passes the box on wire 1 negated on wire 2
-- (the paper's (292), between P ⊗ P).  Semantically the one acts only
-- where wire 2 is 1, the other only where it is 0.  By induction on the
-- width: on four wires decided (Base338Eq); above, the box is expanded
-- by (320) (Gadget322's letters), its rotations are four-wire letters,
-- decided once and weakened (`SemanticSteps.Below`), and its smaller box
-- has wire 3 idle, as has CCZX between P ⊗ P, so that pair is the
-- statement one width down placed around wire 3.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true)
open import Data.List using ([] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem ; Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂ ; eq117 ; eq118)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (module Aj)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; place-• ; place-cong ; place-low)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxZX complete₂ complete₃ using (B₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq299)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMerge complete₂ complete₃ using (eq301 ; eq302)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (eq284 ; E□²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget322 complete₂ complete₃
  using (L ; zx ; xz ; kb ; kb′ ; bb ; lt ; es ; word ; pass-word ; via ; module CW ; E320 ; S-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base338Eq
  using (RW₄ ; Dw₄ ; L-zx ; L-kb ; d-base ; d-zx ; d-kb)

------------------------------------------------------------------------
-- CCZX between P ⊗ P against the box on wire 1 negated on wire 2

-- CCZX and CCXZ between P ⊗ P on the wires 0 1.
RW RV : ∀ {n} → Circuit (₄₊ n)
RW = Aj.⟪ CCZX ⟫
RV = Aj.⟪ CCXZ ⟫

-- The box on wire 1, controlled by wire 0, negatively by wire 2, and by
-- the wires 3 ….
Dw : ∀ j → Circuit (₄₊ j)
Dw j = S₀₁.⟪ N₂.⟪ Λ□ (₃₊ j) ⟫ ⟫

G292 : ℕ → Set
G292 j = (₄₊ j) ⊢ RW • Dw j ≈ Dw j • RW

module _ {j : ℕ} where
  open Tools ((₄₊ j) VRel,_===_)

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

  -- The two conjugations, letter by letter.
  SN-word : ∀ f ls → S₀₁.⟪ N₂.⟪ word f ls ⟫ ⟫ ≈ word (λ l → S₀₁.⟪ N₂.⟪ f l ⟫ ⟫) ls
  SN-word f ls = trans (S₀₁.⟪⟫-cong (CW.⟪⟫-word (X ↑ ↑) X₂² f ls)) (CW.⟪⟫-word (Ex ↓) Ex² (λ l → N₂.⟪ f l ⟫) ls)

  SN-inv : ∀ {w w′} → w • w′ ≈ ε → S₀₁.⟪ N₂.⟪ w ⟫ ⟫ • S₀₁.⟪ N₂.⟪ w′ ⟫ ⟫ ≈ ε
  SN-inv {w} {w′} e = trans (sym (S₀₁.⟪⟫-• _ _))
    (trans (S₀₁.⟪⟫-cong (trans (sym (N₂.⟪⟫-• w w′)) (trans (N₂.⟪⟫-cong e) N₂.⟪⟫-ε))) S₀₁.⟪⟫-ε)

  RW-RV : RW • RV ≈ ε
  RW-RV = trans (sym (Aj.⟪⟫-• CCZX CCXZ)) (trans (Aj.⟪⟫-cong eq117) Aj.⟪⟫-ε)
  RV-RW : RV • RW ≈ ε
  RV-RW = trans (sym (Aj.⟪⟫-• CCXZ CCZX)) (trans (Aj.⟪⟫-cong eq118) Aj.⟪⟫-ε)

module _ {r : ℕ} where
  open Tools ((₄₊ r) VRel,_===_)

  -- X on wire 2 goes inside a placement around wire 3.
  N₂-place : ∀ (V : Circuit (₃₊ r)) → N₂.⟪ place 3 V ⟫ ≈ place 3 (N₂.⟪ V ⟫)
  N₂-place V = sym (trans (place-• 3 (X ↑ ↑) (V • X ↑ ↑))
                 (cong (place-low 3 (X {0} ↑ ↑)) (trans (place-• 3 V (X ↑ ↑)) (back _ (place-low 3 (X {0} ↑ ↑))))))

-- CCZX between P ⊗ P is placed around wire 3.
RW-place : ∀ {r} → (₁₊ (₄₊ r)) ⊢ place 3 (RW {r}) ≈ RW
RW-place = place-low 3 (PP {1} • CCZX {0} • PP {1})

g292 : Comp 4 → ∀ j → Below (₄₊ j) → G292 j
g292 c₄ zero    _ = c₄ (same-sem (RW₄ • Dw₄) (Dw₄ • RW₄) (Evaluated.same d-base))
g292 c₄ (suc j) b = via Dw-word (pass-word _ es letter)
  where
  open Tools ((₄₊ (suc j)) VRel,_===_)
  open WordAlgebra ((₄₊ (suc j)) VRel,_===_) using (comm-inv)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)

  f : L → Circuit (₄₊ (suc j))
  f l = S₀₁.⟪ N₂.⟪ lt (suc j) l ⟫ ⟫

  Dw-word : Dw (suc j) ≈ word f es
  Dw-word = trans (S₀₁.⟪⟫-cong (N₂.⟪⟫-cong (E320 c₄ (suc j) b))) (SN-word (lt (suc j)) es)

  ih : G292 j
  ih = g292 c₄ j (below-suc b)

  -- The rotations: decided on four wires and weakened.
  rZ : RW • f zx ≈ f zx • RW
  rZ = by-sem (RW₄ • L-zx) (L-zx • RW₄) (Evaluated.same d-zx) {suc j}

  rK : RW • f kb ≈ f kb • RW
  rK = by-sem (RW₄ • L-kb) (L-kb • RW₄) (Evaluated.same d-kb) {suc j}

  -- The smaller box: the statement one width down, placed around wire 3.
  pl : f bb ≈ place 3 (Dw j)
  pl = trans (S₀₁.⟪⟫-cong (N₂-place (Λ□ (₃₊ j)))) (S-place (N₂.⟪ Λ□ (₃₊ j) ⟫))

  rB : RW • f bb ≈ f bb • RW
  rB = via pl (begin
    RW • place 3 (Dw j)               ≈⟨ front _ (sym RW-place) ⟩
    place 3 RW • place 3 (Dw j)       ≈⟨ sym (place-• 3 RW (Dw j)) ⟩
    place 3 (RW • Dw j)               ≈⟨ place-cong 3 ih ⟩
    place 3 (Dw j • RW)               ≈⟨ place-• 3 (Dw j) RW ⟩
    place 3 (Dw j) • place 3 RW       ≈⟨ back _ RW-place ⟩
    place 3 (Dw j) • RW ∎)

  letter : ∀ l → RW • f l ≈ f l • RW
  letter zx  = rZ
  letter kb  = rK
  letter xz  = comm-inv (SN-inv eq208′) (SN-inv eq208) rZ
  letter kb′ = comm-inv (SN-inv (trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)))
                        (SN-inv (trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε))) rK
  letter bb  = rB

------------------------------------------------------------------------
-- (338), x = y, at width 5 + k

module XY (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv ; inv-unique)

  private
    Λ W V B E B₁₀ D C₃ : Circuit N
    Λ   = Λ□ (₄₊ k)
    W   = CCZX
    V   = CCXZ
    B   = B□ (₁₊ k)
    E   = Aj.⟪ B ⟫
    B₁₀ = S₀₁.⟪ Λ ⟫
    D   = Dw (₁₊ k)
    C₃  = B₀₁ (₁₊ k)

    Λ² : Λ • Λ ≈ ε
    Λ² = eq299 (₁₊ k) c

    E² : E • E ≈ ε
    E² = E□² (₁₊ k) c

    -- (284), and rotated.
    e284 : Λ ≈ W • E • V • E
    e284 = eq284 (₁₊ k) c

    rot : Λ ≈ E • W • E • V
    rot = inv-unique Λ² inv e284
      where
      inv : (E • W • E • V) • (W • E • V • E) ≈ ε
      inv = begin
        (E • W • E • V) • (W • E • V • E)
          ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
        E • W • E • (V • W) • E • V • E    ≈⟨ back _ (back _ (back _ (trans (front _ eq118) left-unit))) ⟩
        E • W • E • E • V • E              ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ E²) left-unit))) ⟩
        E • W • V • E                      ≈⟨ back _ (trans (sym assoc) (trans (front _ eq117) left-unit)) ⟩
        E • E                              ≈⟨ E² ⟩
        ε ∎

    -- Between P ⊗ P.
    EB : Aj.⟪ E ⟫ ≈ B
    EB = Aj.⟪⟫-⟪⟫ B

    RΛ : Aj.⟪ Λ ⟫ ≈ RW • B • RV • B
    RΛ = trans (Aj.⟪⟫-cong e284) (Aj.⟪⟫-•₄ refl EB refl EB)

    RΛ′ : Aj.⟪ Λ ⟫ ≈ B • RW • B • RV
    RΛ′ = trans (Aj.⟪⟫-cong rot) (Aj.⟪⟫-•₄ EB refl EB refl)

    -- The merges (301), (302) under the swap of the wires 0 1.
    S₀₁-B : S₀₁.⟪ B ⟫ ≈ C₃
    S₀₁-B = begin
      Ex ↓ • ((Ex ↓ • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • Ex ↓)) • Ex ↓
        ≈⟨ by-passoc (□ • ((□ • □ • □) • □ • (□ • □ • □)) • □) (((□ • □) • □ • □) • □ • (□ • □ • (□ • □))) Eq.refl ⟩
      ((Ex ↓ • Ex ↓) • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • (Ex ↓ • Ex ↓))
        ≈⟨ cong (front _ Ex²) (back _ (back _ (back _ Ex²))) ⟩
      (ε • Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑ • ε)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (((□ • □) • □) • □ • (□ • (□ • □))) Eq.refl ⟩
      ((ε • Ex ↑) • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • (Ex ↑ • ε)) ∎

    S₀₁-C₃ : S₀₁.⟪ C₃ ⟫ ≈ B
    S₀₁-C₃ = S₀₁.⟪⟫-≈ˡ (sym S₀₁-B) (S₀₁.⟪⟫-⟪⟫ B)

    merge₁ : B₁₀ • D ≈ B
    merge₁ = S₀₁.⟪⟫-≈ (eq301 (₁₊ k) c) (S₀₁.⟪⟫-• Λ (N₂.⟪ Λ ⟫)) S₀₁-C₃

    merge₂ : D • B₁₀ ≈ B
    merge₂ = S₀₁.⟪⟫-≈ (eq302 (₁₊ k) c) (S₀₁.⟪⟫-• (N₂.⟪ Λ ⟫) Λ) S₀₁-C₃

    B₁₀² : B₁₀ • B₁₀ ≈ ε
    B₁₀² = S₀₁.⟪⟫-invol Λ²

    DD : D • D ≈ ε
    DD = S₀₁.⟪⟫-invol (N₂.⟪⟫-invol Λ²)

    BB₁₀ : B • B₁₀ ≈ D
    BB₁₀ = begin
      B • B₁₀                ≈⟨ front _ (sym merge₂) ⟩
      (D • B₁₀) • B₁₀        ≈⟨ assoc ⟩
      D • (B₁₀ • B₁₀)        ≈⟨ back _ B₁₀² ⟩
      D • ε                  ≈⟨ right-unit ⟩
      D ∎

    B₁₀B : B₁₀ • B ≈ D
    B₁₀B = begin
      B₁₀ • B                ≈⟨ back _ (sym merge₁) ⟩
      B₁₀ • (B₁₀ • D)        ≈⟨ sym assoc ⟩
      (B₁₀ • B₁₀) • D        ≈⟨ front _ B₁₀² ⟩
      ε • D                  ≈⟨ left-unit ⟩
      D ∎

    D-B : D • B ≈ B • D
    D-B = trans DB (sym BD)
      where
      DB : D • B ≈ B₁₀
      DB = trans (back _ (sym merge₂)) (trans (sym assoc) (trans (front _ DD) left-unit))
      BD : B • D ≈ B₁₀
      BD = trans (front _ (sym merge₁)) (trans assoc (trans (back _ DD) right-unit))

    D-RW : D • RW ≈ RW • D
    D-RW = sym (g292 c₄ (₁₊ k) below)

    D-RV : D • RV ≈ RV • D
    D-RV = comm-inv RW-RV RV-RW D-RW

    pass : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    -- Between P ⊗ P the box on wire 1 passes Λ.
    core : Aj.⟪ Λ ⟫ • B₁₀ ≈ B₁₀ • Aj.⟪ Λ ⟫
    core = begin
      Aj.⟪ Λ ⟫ • B₁₀                    ≈⟨ front _ RΛ ⟩
      (RW • B • RV • B) • B₁₀           ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      RW • B • RV • (B • B₁₀)           ≈⟨ back _ (back _ (back _ BB₁₀)) ⟩
      RW • B • RV • D                   ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (RW • B • RV) • D                 ≈⟨ sym (pass D-RW (pass D-B D-RV)) ⟩
      D • RW • B • RV                   ≈⟨ front _ (sym B₁₀B) ⟩
      (B₁₀ • B) • RW • B • RV           ≈⟨ assoc ⟩
      B₁₀ • (B • RW • B • RV)           ≈⟨ back _ (sym RΛ′) ⟩
      B₁₀ • Aj.⟪ Λ ⟫ ∎

  eq338xy : Λ□ (₄₊ k) • Hg (₂₊ k) ≈ Hg (₂₊ k) • Λ□ (₄₊ k)
  eq338xy = Aj.⟪⟫-≈ core (Aj.⟪⟫-•₂ (Aj.⟪⟫-⟪⟫ Λ) refl) (Aj.⟪⟫-•₂ refl (Aj.⟪⟫-⟪⟫ Λ))
