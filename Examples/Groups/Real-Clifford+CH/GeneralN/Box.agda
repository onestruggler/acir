------------------------------------------------------------------------
-- Presentations of groups
--
-- The multi-controlled box on any number of wires (Clément, Lemma D.8,
-- Equations (269)–(273), (286))
--
-- Λ□ k is the box with its box wire on wire 0 and controls on the wires
-- 1 … k.  (269), its decomposition W B V B — W the doubly controlled ZX
-- on the wires 0 1 2 and B the box on wire 1 with controls on the wires
-- 0 3 … k — is its definition.
--
-- (270): Z on a control passes the box.  By induction on k: Z on wire 1
-- or 2 passes W and V, (119)–(122), and becomes, under the transposition
-- of the wires 0 2 that places B, Z on the box wire of the smaller box —
-- the schema (19), or (154) on four wires — or Z on a wire the smaller
-- box does not touch; Z on a higher wire passes W, V and the
-- transposition, and is on a control of the smaller box.
--
-- (272): the box on the wires 1 … k + 1 passes the CZ of the wires 0 1,
-- its box wire and the extra wire.  This is the schema (19) on k + 2
-- wires: Z on wire 0 turns W and V into each other and passes B by (270),
-- so (19) says V B W B = W B V B, that is, W² — the CZ of the wires 1 2 —
-- passes B; the transposition of the wires 0 2 turns this into (272).
--
-- (271): the box one wire up passes the CZ of its first control and the
-- extra wire — (168) for the rotation, and (272) one size down for the
-- smaller box, which that CZ meets on its box wire.
--
-- (286): the box is also V B W B — what (19) says before the square is
-- taken.  (273): the box passes the CZ of its box wire and the control on
-- wire 2, the letter b of W = a b a b: b W = W d b by (128), and d and b
-- pass B, by (19) and by (271) one size down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
open import Presentation.GroupLike using (module Basis-Change)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; Z² ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq154 ; CZ↑-CZ₃₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (eq168)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq119 ; eq120 ; eq121 ; eq122 ; eq123 ; eq124 ; eq128
        ; CCZX² ; CZ₂₀² ; CZ↑-CZ₂₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- Z on a wire

Z[_] : Fin n → Circuit n
Z[_] {₁₊ n} zero    = Z
Z[_] {₁₊ n} (suc i) = Z[ i ] ↑

------------------------------------------------------------------------
-- (269): the definition

eq269 : ∀ k → Λ□ (₃₊ k) ≡ CCZX • τ₀₂-conj (Λ□ (₂₊ k) ↑) • CCXZ • τ₀₂-conj (Λ□ (₂₊ k) ↑)
eq269 k = Eq.refl

------------------------------------------------------------------------
-- The transposition of the wires 0 2

private
  τ₀₂² : (₄₊ n) ⊢ τ₀₂ • τ₀₂ ≈ ε
  τ₀₂² {n} = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)
    where open Tools ((₄₊ n) VRel,_===_)

  module T {n : ℕ} = Conj {₄₊ n} τ₀₂ τ₀₂²

  T-Z₀ : (₄₊ n) ⊢ T.⟪ Z ↓ ⟫ ≈ Z ↑ ↑
  T-Z₀ = L₃-sem (τ₀₂ • Z ↓ • τ₀₂) (Z ↑ ↑) Eq.refl

  T-Z₁ : (₄₊ n) ⊢ T.⟪ Z ↑ ⟫ ≈ Z ↑
  T-Z₁ = L₃-sem (τ₀₂ • Z ↑ • τ₀₂) (Z ↑) Eq.refl

  T-Z₂ : (₄₊ n) ⊢ T.⟪ Z ↑ ↑ ⟫ ≈ Z ↓
  T-Z₂ = L₃-sem (τ₀₂ • Z ↑ ↑ • τ₀₂) (Z ↓) Eq.refl

  T-CZ : (₄₊ n) ⊢ T.⟪ CZ ↑ ⟫ ≈ CZ ↓
  T-CZ = L₃-sem (τ₀₂ • CZ ↑ • τ₀₂) (CZ ↓) Eq.refl

------------------------------------------------------------------------
-- Z on the box wire: (19), and (154) on four wires

box-Z₀ : ∀ k → (₃₊ k) ⊢ Z ↓ • Λ□ (₂₊ k) ≈ Λ□ (₂₊ k) • Z ↓
box-Z₀ 0 = sym (comm-gate₁-w↑ Z-gate (CZ {0}))
  where open Tools (3 VRel,_===_)
box-Z₀ 1 = eq154 {0}
box-Z₀ (₂₊ k) = ax (box-Z k)

------------------------------------------------------------------------
-- (270): Z on a control

eq270 : ∀ k (i : Fin k) → (₁₊ k) ⊢ Z[ suc i ] • Λ□ k ≈ Λ□ k • Z[ suc i ]
eq270 1 zero = refl
  where open Tools (2 VRel,_===_)
eq270 2 zero = lemma-cong↑ (Z ↓ • CZ) (CZ • Z ↓) (by-sem₀ (Z ↓ • CZ) (CZ • Z ↓) Eq.refl)
eq270 2 (suc zero) = lemma-cong↑ (Z ↑ • CZ) (CZ • Z ↑) (by-sem₀ (Z ↑ • CZ) (CZ • Z ↑) Eq.refl)
eq270 (₃₊ k) i = comm-• (z-W i) (comm-• (z-B i) (comm-• (z-V i) (z-B i)))
  where
  open Tools ((₄₊ k) VRel,_===_)
  open Alg ((₄₊ k) VRel,_===_)

  B : Circuit (₄₊ k)
  B = τ₀₂-conj (Λ□ (₂₊ k) ↑)

  z-W : ∀ i → Z[ suc i ] • CCZX ≈ CCZX • Z[ suc i ]
  z-W zero          = eq119
  z-W (suc zero)    = eq121
  z-W (suc (suc i)) = sym (L₃-top CCZX Z[ i ])

  z-V : ∀ i → Z[ suc i ] • CCXZ ≈ CCXZ • Z[ suc i ]
  z-V zero          = eq120
  z-V (suc zero)    = eq122
  z-V (suc (suc i)) = sym (L₃-top CCXZ Z[ i ])

  z-B : ∀ i → Z[ suc i ] • B ≈ B • Z[ suc i ]
  z-B zero = T.⟪⟫-≈ (lemma-cong↑ (Z ↓ • Λ□ (₂₊ k)) (Λ□ (₂₊ k) • Z ↓) (box-Z₀ k))
                    (T.⟪⟫-•₂ T-Z₁ refl) (T.⟪⟫-•₂ refl T-Z₁)
  z-B (suc zero) = T.⟪⟫-≈ (sym (comm-gate₁-w↑ Z-gate (Λ□ (₂₊ k))))
                          (T.⟪⟫-•₂ T-Z₀ refl) (T.⟪⟫-•₂ refl T-Z₀)
  z-B (suc (suc i)) = T.⟪⟫-≈
    (lemma-cong↑ (Z[ suc (suc i) ] • Λ□ (₂₊ k)) (Λ□ (₂₊ k) • Z[ suc (suc i) ]) (eq270 (₂₊ k) (suc i)))
    (T.⟪⟫-•₂ fix refl) (T.⟪⟫-•₂ refl fix)
    where
    fix : T.⟪ Z[ i ] ↑ ↑ ↑ ⟫ ≈ Z[ i ] ↑ ↑ ↑
    fix = T.⟪⟫-fix (L₃-top τ₀₂ Z[ i ])

------------------------------------------------------------------------
-- (272): the content of the schema (19)

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  private
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

  -- If an involution z turns W and V into each other and passes B and
  -- W B V B, then V B W B is W B V B …
  mirror : ∀ {z W V B : Word X} → z • z ≈ ε →
           z • W ≈ V • z → z • V ≈ W • z → z • B ≈ B • z →
           z • (W • B • V • B) ≈ (W • B • V • B) • z →
           V • B • W • B ≈ W • B • V • B
  mirror {z} {W} {V} {B} zz zW zV zB zQ = begin
    V • B • W • B                 ≈⟨ sym right-unit ⟩
    (V • B • W • B) • ε           ≈⟨ back _ (sym zz) ⟩
    (V • B • W • B) • z • z       ≈⟨ sym assoc ⟩
    ((V • B • W • B) • z) • z     ≈⟨ front _ (sym (push₄ zW zB zV zB)) ⟩
    (z • (W • B • V • B)) • z     ≈⟨ front _ zQ ⟩
    ((W • B • V • B) • z) • z     ≈⟨ cancelʳ _ zz ⟩
    W • B • V • B ∎

  -- … and then W² passes B.  B need not be an involution: it is
  -- cancelled by `rcancel`.
  square-passes : ∀ {W V B : Word X} →
                  (∀ {u v} → u • B ≈ v • B → u ≈ v) →
                  W • V ≈ ε → V • W ≈ ε →
                  V • B • W • B ≈ W • B • V • B →
                  (W • W) • B ≈ B • (W • W)
  square-passes {W} {V} {B} rcancel WV VW e = sym (begin
    B • (W • W)           ≈⟨ sym assoc ⟩
    (B • W) • W           ≈⟨ front _ e₂ ⟩
    (W • W • B • V) • W   ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    W • W • B • (V • W)   ≈⟨ back _ (back _ (trans (back _ VW) right-unit)) ⟩
    W • W • B             ≈⟨ sym assoc ⟩
    (W • W) • B ∎)
    where
    e₁ : V • B • W ≈ W • B • V
    e₁ = rcancel (trans (by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl)
                 (trans e (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)))

    e₂ : B • W ≈ W • W • B • V
    e₂ = begin
      B • W                 ≈⟨ sym left-unit ⟩
      ε • B • W             ≈⟨ front _ (sym WV) ⟩
      (W • V) • B • W       ≈⟨ assoc ⟩
      W • V • B • W         ≈⟨ back _ e₁ ⟩
      W • W • B • V ∎

-- The letter B of the box with k + 3 controls: the smaller box on wire 1,
-- its controls on the wires 0 3 … k + 3.
B□ : ∀ k → Circuit (₄₊ k)
B□ k = τ₀₂-conj (Λ□ (₂₊ k) ↑)

-- (286): the box is also V B W B.  On four wires this is (124) and the
-- fact that the CZ of the wires 1 2 passes the CZ from wire 3; above, it
-- is the schema (19).
eq286 : ∀ k → (₄₊ k) ⊢ Λ□ (₃₊ k) ≈ CCXZ • B□ k • CCZX • B□ k
eq286 0 = sym (trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)
         (trans (front _ (flip-WcV (sym eq124) V-dW CZ↑-CZ₃₀))
                (by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl)))
  where
  open Tools (4 VRel,_===_)
  open Alg (4 VRel,_===_)
  V-dW : CCXZ ≈ CZ ↑ • CCZX
  V-dW = begin
    CCXZ                      ≈⟨ sym eq124 ⟩
    CCZX • CZ ↑               ≈⟨ back _ (sym CCZX²) ⟩
    CCZX • CCZX • CCZX        ≈⟨ sym assoc ⟩
    (CCZX • CCZX) • CCZX      ≈⟨ front _ CCZX² ⟩
    CZ ↑ • CCZX ∎
eq286 (₁₊ k) = sym (mirror Γ Z² z-W eq123 z-B (ax (box-Z k)))
  where
  Γ = (₁₊ (₄₊ k)) VRel,_===_
  open Tools Γ

  z-W : Z ↓ • CCZX ≈ CCXZ • Z ↓
  z-W = sym (conj-comm Z² (trans (sym assoc) (trans (front _ eq123) (cancelʳ _ Z²))))

  z-B : Z ↓ • B□ (₁₊ k) ≈ B□ (₁₊ k) • Z ↓
  z-B = T.⟪⟫-≈ (lemma-cong↑ (Z ↑ • Λ□ (₃₊ k)) (Λ□ (₃₊ k) • Z ↑) (eq270 (₃₊ k) zero))
               (T.⟪⟫-•₂ T-Z₂ refl) (T.⟪⟫-•₂ refl T-Z₂)

-- So the CZ of the wires 1 2, the square of W, passes B.
d-B□ : ∀ k → (₄₊ k) ⊢ CZ ↑ • B□ k ≈ B□ k • CZ ↑
d-B□ 0 = CZ↑-CZ₃₀
d-B□ (₁₊ k) = trans (front _ (sym CCZX²))
             (trans (square-passes Γ rcancel eq117 eq118 (sym (eq286 (₁₊ k)))) (back _ CCZX²))
  where
  Γ = (₁₊ (₄₊ k)) VRel,_===_
  open Tools Γ
  open Basis-Change (Gen (₁₊ (₄₊ k))) Γ grouplike using (bbc)

  rcancel : ∀ {u v} → u • B□ (₁₊ k) ≈ v • B□ (₁₊ k) → u ≈ v
  rcancel e = bbc ε (B□ (₁₊ k)) (back ε e)

eq272 : ∀ k → (₁₊ (₄₊ k)) ⊢ CZ ↓ • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • CZ ↓
eq272 k = T.⟪⟫-≈ (d-B□ (₁₊ k)) (T.⟪⟫-•₂ T-CZ (T.⟪⟫-⟪⟫ (Λ□ (₃₊ k) ↑)))
                               (T.⟪⟫-•₂ (T.⟪⟫-⟪⟫ (Λ□ (₃₊ k) ↑)) T-CZ)

------------------------------------------------------------------------
-- (271): the CZ of a control and the extra wire
--
-- The box one wire up is W ↑ B ↑ V ↑ B ↑.  The CZ of the wires 0 2 passes
-- the rotation W ↑ by (168); and B ↑ is the smaller box two wires up —
-- which it meets on its box wire, (272) one size down under the lower
-- swap — between transpositions of the wires 1 3, which it passes.

eq271 : ∀ k → (₁₊ (₄₊ k)) ⊢ CZ₂₀ • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • CZ₂₀
eq271 k = comm-• c-W (comm-• c-B (comm-• c-V c-B))
  where
  Γ = (₁₊ (₄₊ k)) VRel,_===_
  open Tools Γ
  open Alg Γ

  Y : Circuit (₁₊ (₄₊ k))
  Y = Λ□ (₂₊ k) ↑ ↑

  -- The smaller box two wires up.
  c-Y : ∀ k → (₁₊ (₄₊ k)) ⊢ CZ₂₀ • Λ□ (₂₊ k) ↑ ↑ ≈ Λ□ (₂₊ k) ↑ ↑ • CZ₂₀
  c-Y 0 = L₃-top CZ₂₀ CZ
  c-Y (₁₊ j) = S₀₁.⟪⟫-≈
    (lemma-cong↑ (CZ ↓ • Λ□ (₃₊ j) ↑) (Λ□ (₃₊ j) ↑ • CZ ↓) (eq272 j))
    (S₀₁.⟪⟫-•₂ PB.refl (P₂₃-S₀₁ (Λ□ (₃₊ j)))) (S₀₁.⟪⟫-•₂ (P₂₃-S₀₁ (Λ□ (₃₊ j))) PB.refl)

  -- The transposition of the wires 1 3, as three swaps.
  θ : Circuit (₁₊ (₄₊ k)) → Circuit (₁₊ (₄₊ k))
  θ w = S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ w ⟫ ⟫ ⟫

  θ-c : θ CZ₂₀ ≈ CZ₂₀
  θ-c = trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (sym (O-L CZ))) (S₁₂.⟪⟫-⟪⟫ (CZ ↓)))))
       (trans (S₁₂.⟪⟫-cong (L-S₂₃ CZ)) (O-L CZ))

  θ-• : ∀ x y → θ (x • y) ≈ θ x • θ y
  θ-• x y = trans (S₁₂.⟪⟫-cong (trans (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-• x y)) (S₂₃.⟪⟫-• _ _)))
                  (S₁₂.⟪⟫-• _ _)

  B↑-form : τ₀₂-conj (Λ□ (₂₊ k) ↑) ↑ ≈ θ Y
  B↑-form = by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl

  c-B : CZ₂₀ • τ₀₂-conj (Λ□ (₂₊ k) ↑) ↑ ≈ τ₀₂-conj (Λ□ (₂₊ k) ↑) ↑ • CZ₂₀
  c-B = begin
    CZ₂₀ • τ₀₂-conj (Λ□ (₂₊ k) ↑) ↑   ≈⟨ cong (sym θ-c) B↑-form ⟩
    θ CZ₂₀ • θ Y                       ≈⟨ sym (θ-• CZ₂₀ Y) ⟩
    θ (CZ₂₀ • Y)                       ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (c-Y k))) ⟩
    θ (Y • CZ₂₀)                       ≈⟨ θ-• Y CZ₂₀ ⟩
    θ Y • θ CZ₂₀                       ≈⟨ cong (sym B↑-form) θ-c ⟩
    τ₀₂-conj (Λ□ (₂₊ k) ↑) ↑ • CZ₂₀ ∎

  c-W : CZ₂₀ • CCZX ↑ ≈ CCZX ↑ • CZ₂₀
  c-W = eq168

  c-V : CZ₂₀ • CCXZ ↑ ≈ CCXZ ↑ • CZ₂₀
  c-V = comm-inv (lemma-cong↑ (CCZX • CCXZ) ε eq117) (lemma-cong↑ (CCXZ • CCZX) ε eq118) c-W

------------------------------------------------------------------------
-- (273): the CZ of the box wire and the control on wire 2
--
-- It is the letter b of W = a b a b, and b W = W d b with d the CZ of the
-- wires 1 2, (128).  Both d and b pass B — d by the schema (19), above,
-- and b because under the transposition that places B it is the CZ of
-- the smaller box's first control and the extra wire, (271).

private
  T-b : (₄₊ n) ⊢ T.⟪ CZ₂₀ ⟫ ≈ CZ₂₀
  T-b = L₃-sem (τ₀₂ • CZ₂₀ • τ₀₂) CZ₂₀ Eq.refl

  b-Λ↑ : ∀ k → (₄₊ k) ⊢ CZ₂₀ • Λ□ (₂₊ k) ↑ ≈ Λ□ (₂₊ k) ↑ • CZ₂₀
  b-Λ↑ 0      = comm-02-23 CZ CZ (evaluated Eq.refl)
  b-Λ↑ (₁₊ k) = eq271 k

b-B□ : ∀ k → (₄₊ k) ⊢ CZ₂₀ • B□ k ≈ B□ k • CZ₂₀
b-B□ k = T.⟪⟫-≈ (b-Λ↑ k) (T.⟪⟫-•₂ T-b PB.refl) (T.⟪⟫-•₂ PB.refl T-b)

eq273 : ∀ k → (₄₊ k) ⊢ CZ₂₀ • Λ□ (₃₊ k) ≈ Λ□ (₃₊ k) • CZ₂₀
eq273 k = box-pass₂ (invol-comm d² CZ₂₀² CZ↑-CZ₂₀) eq117 eq118 CZ₂₀² eq128
                    (sym (comm-• (sym (d-B□ k)) (sym (b-B□ k)))) (b-B□ k)
  where
  open Tools ((₄₊ k) VRel,_===_)
  open Alg ((₄₊ k) VRel,_===_)
  d² : CZ ↑ • CZ ↑ ≈ ε
  d² = lemma-cong↑ (CZ • CZ) ε CZ²
