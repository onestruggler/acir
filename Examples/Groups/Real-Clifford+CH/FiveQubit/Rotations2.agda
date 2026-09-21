------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation of wire 0 with a control on wire 4 against
-- rotations on the wires 0–3 (Clément, Lemma D.7, Equation (261))
--
-- The gate F rotates wire 0 from the wires 1, 4 and, negatively, 2.
-- (261), at the end of the file, is F against the doubly controlled XZ
-- from the wires 2 3.  First, F against the triply controlled XZ from the
-- wires 1 2 3 (`F₂₆₁-XZ₃`), which needs more and brings (249) to the
-- gates of the four-qubit development (`CZ-P`, `e249`).  With a the CH of the
-- wires 0 1, the definitions are F = a °B₄ a °B₄ and XZ = B a B a — B the
-- box on wire 1 from the wires 0 2 3, °B₄ the one from the wires 0 °2 4 —
-- and the four letters B, a B a, °B₄, a °B₄ a commute pairwise as soon as
-- B passes °B₄ and a °B₄ a = F °B₄, that is, °B₄ and F:
--
--   B passes F in its form °G c °G c, (212): the H gate °G has moved its
--     box wire back to wire 3 (`Shift`) and B passes it by (181); c is the
--     CZ of the wires 0 4 — B is invariant under the transposition of its
--     box wire and wire 4, and passes the CZ of the wires 0 1, (160).
--   B passes °B₄ = B₄ c, (170): B and B₄ are Ŵ c₃ V̂ c₃ and Ŵ c₄ V̂ c₄ with
--     the CZs onto wire 1 from the wires 3 and 4, and each passes the
--     other's CZ — (249), carried along P (`CZ-P`) and the transposition
--     (1 3).
--
-- The paper uses completeness on four qubits four times here; a four-wire
-- evaluation is out of reach, and none is needed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations2
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; comm-↓↑ ; CZ² ; CH²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P ; CZ₃₀² ; CZ₃₀-CZ₂₀ ; CH₃₀-P ; CH₃₀²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq160 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCXZ₂₃ ; eq176)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; ΛH₂′-rot ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (N₂-box₃′ ; °CZ₂₀-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (Ex₁² ; far ; braid↑ ; braid-conj↑ ; module T₁₃ ; T₁₃-nest ; S₁₂-P₀₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (S₂₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (box₃‴)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; ΛH₂′² ; box₃′² ; eq170ᵇ ; eq212)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (CCXZ₁₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃
  using (°ZX₃-as-GBGB)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Auxiliary complete₂ complete₃
  using (box₃↑ ; eq249)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Colours complete₂ complete₃
  using (rot-comm ; cycle₁₄ ; cycle₁₄-•₂ ; cycle₁₄-inj ; cycle₁₄-°box)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq117 ; eq118 ; eq127)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gate

-- The ZX on wire 0 from the wires 1, 4 and, negatively, 2.
F₂₆₁ : Circuit (₁₊ (₄₊ n))
F₂₆₁ = S₃₄.⟪ N₂.⟪ ZX₃ ⟫ ⟫

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ
  open Alg Γ

  -- Two boxes over the same rotation, each passing the other's CZ.
  two-boxes : ∀ {W V c d : Word X} → W • V ≈ ε → V • W ≈ ε → c • c ≈ ε → d • d ≈ ε →
              c • d ≈ d • c →
              (W • c • V • c) • d ≈ d • (W • c • V • c) →
              (W • d • V • d) • c ≈ c • (W • d • V • d) →
              (W • c • V • c) • (W • d • V • d) ≈ (W • d • V • d) • (W • c • V • c)
  two-boxes {W} {V} {c} {d} WV VW cc dd cd Bd B′c = begin
    (W • c • V • c) • (W • d • V • d)
      ≈⟨ cong split split ⟩
    (x • c) • (y • d)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    x • (c • y) • d
      ≈⟨ back _ (front _ (sym yc)) ⟩
    x • (y • c) • d
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (x • y) • (c • d)
      ≈⟨ cong xy cd ⟩
    (y • x) • (d • c)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    y • (x • d) • c
      ≈⟨ back _ (front _ xd) ⟩
    y • (d • x) • c
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (y • d) • (x • c)
      ≈⟨ sym (cong split split) ⟩
    (W • d • V • d) • (W • c • V • c) ∎
    where
    x y : Word X
    x = W • c • V
    y = W • d • V

    split : ∀ {e : Word X} → W • e • V • e ≈ (W • e • V) • e
    split = by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl

    -- x = B c and y = B′ d.
    x-form : x ≈ (W • c • V • c) • c
    x-form = trans (sym (cancelʳ _ cc)) (front _ (sym split))

    y-form : y ≈ (W • d • V • d) • d
    y-form = trans (sym (cancelʳ _ dd)) (front _ (sym split))

    xd : x • d ≈ d • x
    xd = trans (front _ x-form) (trans (sym (comm-• (sym Bd) (sym cd))) (back _ (sym x-form)))

    yc : y • c ≈ c • y
    yc = trans (front _ y-form) (trans (sym (comm-• (sym B′c) cd)) (back _ (sym y-form)))

    xy : x • y ≈ y • x
    xy = begin
      (W • c • V) • (W • d • V)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      W • c • (V • W) • d • V
        ≈⟨ back _ (back _ (cancelˢ′ VW)) ⟩
      W • c • d • V
        ≈⟨ back _ (trans (sym assoc) (trans (front _ cd) assoc)) ⟩
      W • d • c • V
        ≈⟨ back _ (back _ (sym (cancelˢ′ VW))) ⟩
      W • d • (V • W) • c • V
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
      (W • d • V) • (W • c • V) ∎
      where
      cancelˢ′ : ∀ {u v s : Word X} → u • v ≈ ε → (u • v) • s ≈ s
      cancelˢ′ e = trans (front _ e) left-unit

------------------------------------------------------------------------
-- Four-wire facts

private
  S₀₁-CZ : (₄₊ n) ⊢ S₀₁.⟪ CZ ↓ ⟫ ≈ CZ ↓
  S₀₁-CZ = L-sem (Ex • CZ • Ex) CZ Eq.refl

  -- A gate from wire 3 to wire 0, spelled from the pair 0 1 upwards.
  spell : (u : Circuit 2) → (₄₊ n) ⊢ P₀₃ u ≈ S₂₃.⟪ S₁₂.⟪ L u ⟫ ⟫
  spell {n} u = sym (trans (S₂₃.⟪⟫-cong (O-L u)) (O-S₂₃ u))
    where open Tools ((₄₊ n) VRel,_===_)

  -- The CZ of the wires 0 1 through the cycle of the wires 0–3.
  CZ-φ : (₄₊ n) ⊢ CZ ↓ • φ ≈ φ • P₀₃ CZ
  CZ-φ {n} = trans (push-φ (CZ ↓))
    (back _ (trans (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong S₀₁-CZ)) (sym (spell CZ))))
    where open Tools ((₄₊ n) VRel,_===_)

  -- The box on wire 1 passes the CZ of the wires 0 1: (160) under the
  -- lower swap.
  B-CZ↓ : (₄₊ n) ⊢ box₃′ • CZ ↓ ≈ CZ ↓ • box₃′
  B-CZ↓ {n} = sym (S₀₁.⟪⟫-≈ eq160 (S₀₁.⟪⟫-•₂ S₀₁-CZ refl) (S₀₁.⟪⟫-•₂ refl S₀₁-CZ))
    where open Tools ((₄₊ n) VRel,_===_)

  -- (1 3) exchanges the boxes on the wires 1 and 3.
  T₁₃-box₃′ : (₄₊ n) ⊢ T₁₃.⟪ box₃′ ⟫ ≈ box₃‴
  T₁₃-box₃′ {n} = trans (T₁₃-nest box₃′) (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong S₂₃-box₃′))
    where open Tools ((₄₊ n) VRel,_===_)

  T₁₃-box₃‴ : (₄₊ n) ⊢ T₁₃.⟪ box₃‴ ⟫ ≈ box₃′
  T₁₃-box₃‴ {n} = trans (T₁₃.⟪⟫-cong (sym T₁₃-box₃′)) (T₁₃.⟪⟫-⟪⟫ box₃′)
    where open Tools ((₄₊ n) VRel,_===_)

  N₂-c : (₄₊ n) ⊢ N₂.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
  N₂-c {n} = begin
    N₂.⟪ CZ₃₀ ⟫       ≈⟨ N₂.⟪⟫-cong CZ₃₀-P ⟩
    N₂.⟪ P₀₃ CZ ⟫     ≈⟨ N₂.⟪⟫-fix (sym (P₀₃-U CZ (X ↑))) ⟩
    P₀₃ CZ            ≈⟨ sym CZ₃₀-P ⟩
    CZ₃₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- (170), solved for the white box.
  °B-split : (₄₊ n) ⊢ S₀₁.⟪ °box₃ ⟫ ≈ box₃′ • CZ₃₀
  °B-split {n} = trans (sym (cancelˡ _ box₃′²)) (back _ eq170ᵇ)
    where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (261)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    W₅ = Circuit (₁₊ (₄₊ n))

    Ex₃₄ CZ₃₄ a B Ŵ V̂ d₃ d₄ e₄ B₄ °B₄ : W₅
    Ex₃₄ = Ex ↑ ↑ ↑
    CZ₃₄ = CZ ↑ ↑ ↑
    a    = CH ↓
    B    = box₃′
    Ŵ    = S₀₁.⟪ CCZX ⟫
    V̂    = S₀₁.⟪ CCXZ ⟫
    d₃   = S₀₁.⟪ CZ₃₀ ⟫
    d₄   = S₃₄.⟪ d₃ ⟫
    e₄   = S₃₄.⟪ CZ₃₀ ⟫
    B₄   = S₃₄.⟪ box₃′ ⟫
    °B₄  = S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫

    --------------------------------------------------------------------
    -- The CZ of the wires 0 1 along P

    c₄-tail : c₄ ≈ φ • Ex₃₄
    c₄-tail = by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl

    CZ-c₄ : CZ ↓ • c₄ ≈ c₄ • S₃₄.⟪ P₀₃ CZ ⟫
    CZ-c₄ = begin
      CZ ↓ • c₄                           ≈⟨ back _ c₄-tail ⟩
      CZ ↓ • φ • Ex₃₄                     ≈⟨ sym assoc ⟩
      (CZ ↓ • φ) • Ex₃₄                   ≈⟨ front _ CZ-φ ⟩
      (φ • P₀₃ CZ) • Ex₃₄                 ≈⟨ assoc ⟩
      φ • P₀₃ CZ • Ex₃₄                   ≈⟨ back _ (sym (cancelˡ _ Ex₃²)) ⟩
      φ • Ex₃₄ • Ex₃₄ • P₀₃ CZ • Ex₃₄     ≈⟨ sym assoc ⟩
      (φ • Ex₃₄) • S₃₄.⟪ P₀₃ CZ ⟫         ≈⟨ front _ (sym c₄-tail) ⟩
      c₄ • S₃₄.⟪ P₀₃ CZ ⟫ ∎

    Φ-e : Φ (S₃₄.⟪ P₀₃ CZ ⟫) ≈ CZ₃₄
    Φ-e = begin
      S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ S₃₄.⟪ P₀₃ CZ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (conj-swap far₀₃ (P₀₃ CZ))) ⟩
      S₂₃.⟪ S₁₂.⟪ S₃₄.⟪ S₀₁.⟪ P₀₃ CZ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (S₃₄.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ)))) ⟩
      S₂₃.⟪ S₁₂.⟪ S₃₄.⟪ P₁₃ CZ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (conj-swap far₁₃ (P₁₃ CZ)) ⟩
      S₂₃.⟪ S₃₄.⟪ S₁₂.⟪ P₁₃ CZ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₃₄.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ (P₂₃ CZ))) ⟩
      S₂₃.⟪ S₃₄.⟪ P₂₃ CZ ⟫ ⟫
        ≈⟨ lemma-cong↑ (U₃ (Ex ↓ • (Ex ↑ • CZ ↓ • Ex ↑) • Ex ↓)) (U₃ (CZ ↑))
                       (U₃-sem (Ex ↓ • (Ex ↑ • CZ ↓ • Ex ↑) • Ex ↓) (CZ ↑) Eq.refl) ⟩
      CZ₃₄ ∎

    CZ-P : CZ ↓ • P ≈ P • CZ₃₄
    CZ-P = begin
      CZ ↓ • c₄ • φ                     ≈⟨ sym assoc ⟩
      (CZ ↓ • c₄) • φ                   ≈⟨ front _ CZ-c₄ ⟩
      (c₄ • S₃₄.⟪ P₀₃ CZ ⟫) • φ         ≈⟨ assoc ⟩
      c₄ • S₃₄.⟪ P₀₃ CZ ⟫ • φ           ≈⟨ back _ (push-φ (S₃₄.⟪ P₀₃ CZ ⟫)) ⟩
      c₄ • φ • Φ (S₃₄.⟪ P₀₃ CZ ⟫)       ≈⟨ back _ (back _ Φ-e) ⟩
      c₄ • φ • CZ₃₄                     ≈⟨ sym assoc ⟩
      P • CZ₃₄ ∎

    -- (249) for the box on wire 3 of the wires 0–3.
    e249 : CZ₃₄ • box₃‴ ≈ box₃‴ • CZ₃₄
    e249 = transport Γ P-cancel CZ-P (F-P (λ m → box₃ {m}) (λ m → Eq.refl)) eq249

    --------------------------------------------------------------------
    -- B passes the CZ from wire 4 onto its box wire: (249) under (1 3)

    d₃-form : d₃ ≈ P₁₃ CZ
    d₃-form = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ))

    d₄-form : d₄ ≈ S₁₂.⟪ S₂₃.⟪ CZ₃₄ ⟫ ⟫
    d₄-form = begin
      S₃₄.⟪ d₃ ⟫
        ≈⟨ S₃₄.⟪⟫-cong d₃-form ⟩
      S₃₄.⟪ S₁₂.⟪ P₂₃ CZ ⟫ ⟫
        ≈⟨ sym (conj-swap far₁₃ (P₂₃ CZ)) ⟩
      S₁₂.⟪ S₃₄.⟪ P₂₃ CZ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (lemma-cong↑ (Ex ↑ ↑ • CZ ↑ • Ex ↑ ↑) (Ex ↑ • CZ ↑ ↑ • Ex ↑)
                        (lemma-cong↑ (Ex ↑ • CZ ↓ • Ex ↑) (Ex ↓ • CZ ↑ • Ex ↓) (O-L CZ))) ⟩
      S₁₂.⟪ S₂₃.⟪ CZ₃₄ ⟫ ⟫ ∎

    T-cz : T₁₃.⟪ CZ₃₄ ⟫ ≈ d₄
    T-cz = begin
      T₁₃.⟪ CZ₃₄ ⟫
        ≈⟨ T₁₃-nest CZ₃₄ ⟩
      S₂₃.⟪ S₁₂.⟪ S₂₃.⟪ CZ₃₄ ⟫ ⟫ ⟫
        ≈⟨ sym (braid-conj↑ CZ₃₄) ⟩
      S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ CZ₃₄ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-fix
             (lemma-cong↑ (Ex ↓ • CZ ↑ ↑) (CZ ↑ ↑ • Ex ↓) (L-comm Ex CZ)))) ⟩
      S₁₂.⟪ S₂₃.⟪ CZ₃₄ ⟫ ⟫
        ≈⟨ sym d₄-form ⟩
      d₄ ∎

    B-d₄ : B • d₄ ≈ d₄ • B
    B-d₄ = sym (T₁₃.⟪⟫-≈ e249 (T₁₃.⟪⟫-•₂ T-cz T₁₃-box₃‴) (T₁₃.⟪⟫-•₂ T₁₃-box₃‴ T-cz))

    --------------------------------------------------------------------
    -- B passes the CZ of the wires 0 4: it is invariant under (1 4)

    τ : W₅ → W₅
    τ w = S₁₂.⟪ S₂₃.⟪ S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ w ⟫ ⟫ ⟫ ⟫ ⟫

    τ-cong : ∀ {x y : W₅} → x ≈ y → τ x ≈ τ y
    τ-cong e = S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong e))))

    τ-• : (x y : W₅) → τ (x • y) ≈ τ x • τ y
    τ-• x y =
      trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₃₄.⟪⟫-cong
              (trans (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-• x y)) (S₂₃.⟪⟫-• _ _)))))
      (trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₃₄.⟪⟫-• _ _)))
      (trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-• _ _)) (S₁₂.⟪⟫-• _ _)))

    τ-B : τ B ≈ B
    τ-B = trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₃₄.⟪⟫-fix Ex₃₄-box₃‴)))
         (trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ B ⟫))) (S₁₂.⟪⟫-⟪⟫ B))

    p′ : W₅
    p′ = S₂₃.⟪ S₁₂.⟪ CZ ↓ ⟫ ⟫

    p′-e₄ : S₃₄.⟪ p′ ⟫ ≈ e₄
    p′-e₄ = S₃₄.⟪⟫-cong (trans (sym (spell CZ)) (sym CZ₃₀-P))

    τ-CZ : τ (CZ ↓) ≈ e₄
    τ-CZ = begin
      S₁₂.⟪ S₂₃.⟪ S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ CZ ↓ ⟫ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (sym (braid-conj₃₄ (S₁₂.⟪ CZ ↓ ⟫))) ⟩
      S₁₂.⟪ S₃₄.⟪ S₂₃.⟪ S₃₄.⟪ S₁₂.⟪ CZ ↓ ⟫ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong
             (S₃₄.⟪⟫-fix (sym (L₃-top (Ex ↑ • CZ ↓ • Ex ↑) Ex))))) ⟩
      S₁₂.⟪ S₃₄.⟪ p′ ⟫ ⟫
        ≈⟨ conj-swap far₁₃ p′ ⟩
      S₃₄.⟪ S₁₂.⟪ p′ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (braid-conj↑ (CZ ↓)) ⟩
      S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ S₂₃.⟪ CZ ↓ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (L-S₂₃ CZ))) ⟩
      S₃₄.⟪ p′ ⟫
        ≈⟨ p′-e₄ ⟩
      e₄ ∎

    B-e₄ : B • e₄ ≈ e₄ • B
    B-e₄ = begin
      B • e₄              ≈⟨ sym (cong τ-B τ-CZ) ⟩
      τ B • τ (CZ ↓)      ≈⟨ sym (τ-• B (CZ ↓)) ⟩
      τ (B • CZ ↓)        ≈⟨ τ-cong B-CZ↓ ⟩
      τ (CZ ↓ • B)        ≈⟨ τ-• (CZ ↓) B ⟩
      τ (CZ ↓) • τ B      ≈⟨ cong τ-CZ τ-B ⟩
      e₄ • B ∎

    --------------------------------------------------------------------
    -- The forms

    N₂-a : N₂.⟪ a ⟫ ≈ a
    N₂-a = N₂.⟪⟫-fix (sym (L-comm CH X))

    S₃₄-a : S₃₄.⟪ a ⟫ ≈ a
    S₃₄-a = S₃₄.⟪⟫-fix (sym (L-comm CH (Ex ↑)))

    F-form₁ : F₂₆₁ ≈ a • °B₄ • a • °B₄
    F-form₁ = trans (S₃₄.⟪⟫-cong (N₂.⟪⟫-•₄ N₂-a N₂-box₃′ N₂-a N₂-box₃′))
                    (S₃₄.⟪⟫-•₄ S₃₄-a refl S₃₄-a refl)

    F-form₂ : F₂₆₁ ≈ °ΛH₂′ • e₄ • °ΛH₂′ • e₄
    F-form₂ = trans (S₃₄.⟪⟫-cong (trans (N₂.⟪⟫-cong eq212) (N₂.⟪⟫-•₄ refl N₂-c refl N₂-c)))
                    (S₃₄.⟪⟫-•₄ fixG refl fixG refl)
      where
      fixG : S₃₄.⟪ °ΛH₂′ ⟫ ≈ °ΛH₂′
      fixG = S₃₄.⟪⟫-fix Ex₃₄-°ΛH₂′

    °B₄-form : °B₄ ≈ B₄ • e₄
    °B₄-form = trans (S₃₄.⟪⟫-cong °B-split) (S₃₄.⟪⟫-• box₃′ CZ₃₀)

    B-form : B ≈ Ŵ • d₃ • V̂ • d₃
    B-form = S₀₁.⟪⟫-•₄ refl refl refl refl

    B₄-form : B₄ ≈ Ŵ • d₄ • V̂ • d₄
    B₄-form = trans (S₃₄.⟪⟫-cong B-form)
      (S₃₄.⟪⟫-•₄ (S₃₄.⟪⟫-fix (sym (L₃-top (Ex ↓ • CCZX • Ex ↓) Ex))) refl
                 (S₃₄.⟪⟫-fix (sym (L₃-top (Ex ↓ • CCXZ • Ex ↓) Ex))) refl)

    --------------------------------------------------------------------
    -- B passes B₄, °B₄ and F

    ŴV̂ : Ŵ • V̂ ≈ ε
    ŴV̂ = trans (sym (S₀₁.⟪⟫-• CCZX CCXZ)) (trans (S₀₁.⟪⟫-cong eq117) S₀₁.⟪⟫-ε)

    V̂Ŵ : V̂ • Ŵ ≈ ε
    V̂Ŵ = trans (sym (S₀₁.⟪⟫-• CCXZ CCZX)) (trans (S₀₁.⟪⟫-cong eq118) S₀₁.⟪⟫-ε)

    d₃² : d₃ • d₃ ≈ ε
    d₃² = S₀₁.⟪⟫-invol CZ₃₀²

    d₄² : d₄ • d₄ ≈ ε
    d₄² = S₃₄.⟪⟫-invol d₃²

    -- The CZs onto wire 1 from the wires 3 and 4: those onto wire 0 from
    -- the wires 2 and 3, one wire up.
    up : CZ₃₀ ↑ ≈ S₁₂.⟪ S₂₃.⟪ CZ₃₄ ⟫ ⟫
    up = lemma-cong↑ CZ₃₀ (P₀₃ CZ) CZ₃₀-P

    d₃-d₄ : d₃ • d₄ ≈ d₄ • d₃
    d₃-d₄ = begin
      d₃ • d₄
        ≈⟨ cong d₃-form (trans d₄-form (sym up)) ⟩
      CZ₂₀ ↑ • CZ₃₀ ↑
        ≈⟨ sym (lemma-cong↑ (CZ₃₀ • CZ₂₀) (CZ₂₀ • CZ₃₀) CZ₃₀-CZ₂₀) ⟩
      CZ₃₀ ↑ • CZ₂₀ ↑
        ≈⟨ sym (cong (trans d₄-form (sym up)) d₃-form) ⟩
      d₄ • d₃ ∎

    B₄-d₃ : B₄ • d₃ ≈ d₃ • B₄
    B₄-d₃ = S₃₄.⟪⟫-≈ B-d₄ (S₃₄.⟪⟫-•₂ refl (S₃₄.⟪⟫-⟪⟫ d₃)) (S₃₄.⟪⟫-•₂ (S₃₄.⟪⟫-⟪⟫ d₃) refl)

    B-B₄ : B • B₄ ≈ B₄ • B
    B-B₄ = trans (cong B-form B₄-form)
          (trans (two-boxes Γ ŴV̂ V̂Ŵ d₃² d₄² d₃-d₄
                   (trans (front _ (sym B-form)) (trans B-d₄ (back _ B-form)))
                   (trans (front _ (sym B₄-form)) (trans B₄-d₃ (back _ B₄-form))))
                 (sym (cong B₄-form B-form)))

    B-°B₄ : B • °B₄ ≈ °B₄ • B
    B-°B₄ = trans (back _ °B₄-form) (trans (comm-• B-B₄ B-e₄) (front _ (sym °B₄-form)))

    B-F : B • F₂₆₁ ≈ F₂₆₁ • B
    B-F = trans (back _ F-form₂) (trans (comm-abab eq181 B-e₄) (front _ (sym F-form₂)))

    --------------------------------------------------------------------
    -- The four letters

    module A = Conj {₁₊ (₄₊ n)} a CH²

    °B₄² : °B₄ • °B₄ ≈ ε
    °B₄² = S₃₄.⟪⟫-invol (S₀₁.⟪⟫-invol (N₂.⟪⟫-invol eq166))

    F-split : F₂₆₁ ≈ A.⟪ °B₄ ⟫ • °B₄
    F-split = trans F-form₁ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)

    B̃₄-form : A.⟪ °B₄ ⟫ ≈ F₂₆₁ • °B₄
    B̃₄-form = sym (trans (front _ F-split) (cancelʳ _ °B₄²))

    B-B̃₄ : B • A.⟪ °B₄ ⟫ ≈ A.⟪ °B₄ ⟫ • B
    B-B̃₄ = trans (back _ B̃₄-form) (trans (comm-• B-F B-°B₄) (front _ (sym B̃₄-form)))

    B̃-°B₄ : A.⟪ B ⟫ • °B₄ ≈ °B₄ • A.⟪ B ⟫
    B̃-°B₄ = A.⟪⟫-≈ B-B̃₄ (A.⟪⟫-•₂ refl (A.⟪⟫-⟪⟫ °B₄)) (A.⟪⟫-•₂ (A.⟪⟫-⟪⟫ °B₄) refl)

    B̃-B̃₄ : A.⟪ B ⟫ • A.⟪ °B₄ ⟫ ≈ A.⟪ °B₄ ⟫ • A.⟪ B ⟫
    B̃-B̃₄ = A.⟪⟫-≈ B-°B₄ (A.⟪⟫-• B °B₄) (A.⟪⟫-• °B₄ B)

    X-°B₄ : XZ₃ • °B₄ ≈ °B₄ • XZ₃
    X-°B₄ = sym (comm-• (sym B-°B₄) (sym B̃-°B₄))

    X-B̃₄ : XZ₃ • A.⟪ °B₄ ⟫ ≈ A.⟪ °B₄ ⟫ • XZ₃
    X-B̃₄ = sym (comm-• (sym B-B̃₄) (sym B̃-B̃₄))

  -- The rotation passes the triply controlled XZ on the wires 0–3.
  F₂₆₁-XZ₃ : F₂₆₁ • XZ₃ ≈ XZ₃ • F₂₆₁
  F₂₆₁-XZ₃ = sym (trans (back _ F-split) (trans (comm-• X-B̃₄ X-°B₄) (front _ (sym F-split))))

------------------------------------------------------------------------
-- (261): the rotation against the doubly controlled XZ from the wires 2 3
--
-- The rotation is °G °B₄ °G °B₄, (210) negated on wire 2 with the box wire
-- of its H gate back on wire 3.  The H gate passes the XZ in its form
-- c h c h with the roles of the controls exchanged, (14): c is the CZ
-- from wire 2, of the other colour, and h the CH from wire 3, around
-- which the H gate is a rotation.  The box has its box wire on wire 1 and
-- needs wire 4; under the cycle that carries wire 1 to wire 4 it is the
-- box on wire 2 of the wires 0–3 (`cycle₁₄-°box`) and the XZ the one on
-- the wires 0 1 2, and the equation is (176) negated on wire 2, under the
-- middle swap.

private
  -- The doubly controlled XZ with the roles of its controls exchanged.
  CCXZ-alt : (₃₊ n) ⊢ CCXZ ≈ CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀
  CCXZ-alt {n} = inv-unique eq117 (invol-abab CZ² (O-invol CH CH²)) (ax symm-controls)
    where open Alg ((₃₊ n) VRel,_===_)

  V₂₃-alt : (₄₊ n) ⊢ CCXZ₂₃ ≈ CZ₂₀ • P₀₃ CH • CZ₂₀ • P₀₃ CH
  V₂₃-alt {n} = trans (S₀₁.⟪⟫-cong (lemma-cong↑ CCXZ (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀) CCXZ-alt))
                      (S₀₁.⟪⟫-•₄ refl refl refl refl)
    where open Tools ((₄₊ n) VRel,_===_)

  -- The H gate is a rotation around the CH from its box wire, so it
  -- passes it.
  e-ΛH₂′ : (₄₊ n) ⊢ P₀₃ CH • ΛH₂′ ≈ ΛH₂′ • P₀₃ CH
  e-ΛH₂′ {n} = trans (back _ ΛH₂′-rot) (trans (rot-comm Γ e² WV VW rr) (front _ (sym ΛH₂′-rot)))
    where
    Γ = (₄₊ n) VRel,_===_
    open Tools Γ
    open Alg Γ
    d s e : Circuit (₄₊ n)
    d = P₂₃ CZ
    s = P₁₃ HC
    e = P₀₃ CH
    d² : d • d ≈ ε
    d² = lemma-cong↑ (U (CZ • CZ)) ε (U-sem (CZ • CZ) ε Eq.refl)
    s² : s • s ≈ ε
    s² = conj-invol Ex₁² (lemma-cong↑ (U (HC • HC)) ε (U-sem (HC • HC) ε Eq.refl))
    e² : e • e ≈ ε
    e² = trans (sym (cong CH₃₀-P CH₃₀-P)) CH₃₀²
    WV : (s • d • s • d) • (d • s • d • s) ≈ ε
    WV = invol-abab s² d²
    VW : (d • s • d • s) • (s • d • s • d) ≈ ε
    VW = invol-abab d² s²
    rr : ((d • s • d • s) • e • (s • d • s • d) • e) • ((d • s • d • s) • e • (s • d • s • d) • e) ≈ ε
    rr = trans (sym (cong ΛH₂′-rot ΛH₂′-rot)) ΛH₂′²

  N₂-e : (₄₊ n) ⊢ N₂.⟪ P₀₃ CH ⟫ ≈ P₀₃ CH
  N₂-e {n} = N₂.⟪⟫-fix (sym (P₀₃-U CH (X ↑)))
    where open Tools ((₄₊ n) VRel,_===_)

  °G-V₂₃ : (₄₊ n) ⊢ °ΛH₂′ • CCXZ₂₃ ≈ CCXZ₂₃ • °ΛH₂′
  °G-V₂₃ {n} = trans (back _ V₂₃-alt) (trans (comm-abab °G-c °G-e) (front _ (sym V₂₃-alt)))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    °G-c : °ΛH₂′ • CZ₂₀ ≈ CZ₂₀ • °ΛH₂′
    °G-c = sym (N₂.⟪⟫-≈ °CZ₂₀-ΛH₂′ (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CZ₂₀) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ CZ₂₀)))
    °G-e : °ΛH₂′ • P₀₃ CH ≈ P₀₃ CH • °ΛH₂′
    °G-e = sym (N₂.⟪⟫-≈ e-ΛH₂′ (N₂.⟪⟫-•₂ N₂-e refl) (N₂.⟪⟫-•₂ refl N₂-e))

  -- (176), negated on wire 2 and under the middle swap.
  Y₂-V : (₄₊ n) ⊢ S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ • CCXZ ≈ CCXZ • S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫
  Y₂-V {n} = sym (S₁₂.⟪⟫-≈ e₁ (S₁₂.⟪⟫-•₂ S₁₂-V refl) (S₁₂.⟪⟫-•₂ refl S₁₂-V))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    e₁ : CCXZ • S₀₁.⟪ °box₃ ⟫ ≈ S₀₁.⟪ °box₃ ⟫ • CCXZ
    e₁ = N₂.⟪⟫-≈ eq176 (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CCXZ) N₂-box₃′) (N₂.⟪⟫-•₂ N₂-box₃′ (N₂.⟪⟫-⟪⟫ CCXZ))
    S₁₂-V : S₁₂.⟪ CCXZ ⟫ ≈ CCXZ
    S₁₂-V = S₁₂.⟪⟫-fix (comm-inv eq117 eq118 (sym eq127))

  -- The middle swap on the doubly controlled XZ from the wires 1 3.
  S₁₂-CCXZ₁₃ : (₄₊ n) ⊢ S₁₂.⟪ CCXZ₁₃ ⟫ ≈ CCXZ₂₃
  S₁₂-CCXZ₁₃ {n} = begin
    S₁₂.⟪ CCXZ₁₃ ⟫
      ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-•₄ (O-S₂₃ CZ) (L-S₂₃ CH) (O-S₂₃ CZ) (L-S₂₃ CH)) ⟩
    S₁₂.⟪ P₀₃ CZ • CH ↓ • P₀₃ CZ • CH ↓ ⟫
      ≈⟨ S₁₂.⟪⟫-•₄ (S₁₂-P₀₃ CZ) (O-L CH) (S₁₂-P₀₃ CZ) (O-L CH) ⟩
    P₀₃ CZ • CH₂₀ • P₀₃ CZ • CH₂₀
      ≈⟨ sym (S₀₁.⟪⟫-•₄ refl refl refl refl) ⟩
    CCXZ₂₃ ∎
    where open Tools ((₄₊ n) VRel,_===_)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    °B₄ : Circuit (₁₊ (₄₊ n))
    °B₄ = S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫

    F-form₃ : F₂₆₁ ≈ °ΛH₂′ • °B₄ • °ΛH₂′ • °B₄
    F-form₃ = trans (S₃₄.⟪⟫-cong °ZX₃-as-GBGB) (S₃₄.⟪⟫-•₄ fixG refl fixG refl)
      where
      fixG : S₃₄.⟪ °ΛH₂′ ⟫ ≈ °ΛH₂′
      fixG = S₃₄.⟪⟫-fix Ex₃₄-°ΛH₂′

    -- The XZ under the cycle that carries wire 1 to wire 4.
    cycle-V : cycle₁₄ CCXZ₂₃ ≈ CCXZ
    cycle-V = begin
      S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ CCXZ₂₃ ⟫ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (sym S₁₂-CCXZ₁₃)) (S₁₂.⟪⟫-⟪⟫ CCXZ₁₃))) ⟩
      S₃₄.⟪ S₂₃.⟪ CCXZ₁₃ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ (L₃ CCXZ)) ⟩
      S₃₄.⟪ CCXZ ⟫
        ≈⟨ S₃₄.⟪⟫-fix (sym (L₃-top CCXZ Ex)) ⟩
      CCXZ ∎

    °B₄-V₂₃ : °B₄ • CCXZ₂₃ ≈ CCXZ₂₃ • °B₄
    °B₄-V₂₃ = cycle₁₄-inj (trans (cycle₁₄-•₂ cycle₁₄-°box cycle-V)
                          (trans Y₂-V (sym (cycle₁₄-•₂ cycle-V cycle₁₄-°box))))

  eq261 : F₂₆₁ • CCXZ₂₃ ≈ CCXZ₂₃ • F₂₆₁
  eq261 = trans (front _ F-form₃)
         (trans (sym (comm-abab (sym °G-V₂₃) (sym °B₄-V₂₃))) (back _ (sym F-form₃)))
