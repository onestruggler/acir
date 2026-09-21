------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P on the target of a rotation and the fifth wire turns the
-- rotation over: (262) for the gates on the wires 0–3
--
-- (262) is about the rotation one wire up, its target on wire 1, and
-- P ⊗ P on the wires 0 1.  Along P = c₄ φ of `Shift` a symmetric
-- two-wire circuit on the wires 0 1 becomes the same circuit on the
-- wires 3 4 (`pair-P`: through φ it is the circuit on the wires 0 3,
-- through the last swap of c₄ the one on the wires 0 4, and through φ
-- again the one on the wires 3 4 — one three-wire evaluation), and the
-- rotation becomes the one of wire 3; the three lower swaps bring the
-- target back to wire 0 and P ⊗ P to the wires 0 4 (`PP₀₄`).  X on the
-- wires 1, 2, 3 passes `PP₀₄`, which gives the rotations with white
-- controls, and the lower and the middle swap carry target and P ⊗ P to
-- the wires 2 and 2 4 (`PP₂₄`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Pairs
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₃ ; PP₀₃²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (PP₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies245 complete₂ complete₃
  using (N₂ᵇ ; S₂₄₅)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations complete₂ complete₃
  using (eq262)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The gates

-- P ⊗ P on the wires 0 4 and 2 4.
PP₀₄ PP₂₄ : Circuit (₁₊ (₄₊ n))
PP₀₄ = S₃₄.⟪ PP₀₃ ⟫
PP₂₄ = S₃₄.⟪ PP₂₃ ⟫

-- The rotation of wire 0 from wire 1, from wire 3 negatively, and from
-- wire 2 in either colour; and the same with its target on wire 2 and
-- the coloured control on wire 1.
V₂₆₃ J₂₆₃ : Bool → Bool → Circuit (₄₊ n)
V₂₆₃ α b = N₃.⟪ N₂ᵇ α (rot b) ⟫
J₂₆₃ α b = S₁₂.⟪ S₀₁.⟪ V₂₆₃ α b ⟫ ⟫

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  -- An equation x y = z x carried along a word.
  transport₂ : ∀ {p x x′ y y′ z z′ : Word X} →
               (∀ {u v} → p • u ≈ p • v → u ≈ v) →
               x • p ≈ p • x′ → y • p ≈ p • y′ → z • p ≈ p • z′ →
               x • y ≈ z • x → x′ • y′ ≈ z′ • x′
  transport₂ {p} {x} {x′} {y} {y′} {z} {z′} cancel xp yp zp xy = cancel (begin
    p • x′ • y′       ≈⟨ sym assoc ⟩
    (p • x′) • y′     ≈⟨ front _ (sym xp) ⟩
    (x • p) • y′      ≈⟨ assoc ⟩
    x • p • y′        ≈⟨ back _ (sym yp) ⟩
    x • y • p         ≈⟨ sym assoc ⟩
    (x • y) • p       ≈⟨ front _ xy ⟩
    (z • x) • p       ≈⟨ assoc ⟩
    z • x • p         ≈⟨ back _ xp ⟩
    z • p • x′        ≈⟨ sym assoc ⟩
    (z • p) • x′      ≈⟨ front _ zp ⟩
    (p • z′) • x′     ≈⟨ assoc ⟩
    p • z′ • x′ ∎)

  -- x turns y into y′ and back.
  flip-pass : ∀ {x w w′ : Word X} → x • x ≈ ε → x • w ≈ w′ • x → x • w′ ≈ w • x
  flip-pass xx e = sym (conj-comm xx (trans (sym assoc) (trans (front _ e) (cancelʳ _ xx))))

------------------------------------------------------------------------
-- A symmetric two-wire circuit along P

private
  spell : (u : Circuit 2) → (₄₊ n) ⊢ P₀₃ u ≈ S₂₃.⟪ S₁₂.⟪ L u ⟫ ⟫
  spell {n} u = sym (trans (S₂₃.⟪⟫-cong (O-L u)) (O-S₂₃ u))
    where open Tools ((₄₊ n) VRel,_===_)

module _ (u : Circuit 2)
         (u-sym : ∀ {m} → (₄₊ m) ⊢ S₀₁.⟪ L u ⟫ ≈ L u)
         (u-up : ∀ {m} → (₁₊ (₄₊ m)) ⊢ S₂₃.⟪ S₃₄.⟪ P₂₃ u ⟫ ⟫ ≈ P₂₃ u ↑)
         where

  private
    u-φ : (₄₊ n) ⊢ L u • φ ≈ φ • P₀₃ u
    u-φ {n} = trans (push-φ (L u))
      (back _ (trans (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong u-sym)) (sym (spell u))))
      where open Tools ((₄₊ n) VRel,_===_)

  pair-P : (₁₊ (₄₊ n)) ⊢ L u • P ≈ P • P₂₃ u ↑
  pair-P {n} = begin
    L u • c₄ • φ
      ≈⟨ sym assoc ⟩
    (L u • c₄) • φ
      ≈⟨ front _ u-c₄ ⟩
    (c₄ • S₃₄.⟪ P₀₃ u ⟫) • φ
      ≈⟨ assoc ⟩
    c₄ • S₃₄.⟪ P₀₃ u ⟫ • φ
      ≈⟨ back _ (push-φ (S₃₄.⟪ P₀₃ u ⟫)) ⟩
    c₄ • φ • Φ (S₃₄.⟪ P₀₃ u ⟫)
      ≈⟨ back _ (back _ Φ-u) ⟩
    c₄ • φ • P₂₃ u ↑
      ≈⟨ sym assoc ⟩
    P • P₂₃ u ↑ ∎
    where
    open Tools ((₁₊ (₄₊ n)) VRel,_===_)

    c₄-tail : c₄ ≈ φ • Ex ↑ ↑ ↑
    c₄-tail = by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl

    u-c₄ : L u • c₄ ≈ c₄ • S₃₄.⟪ P₀₃ u ⟫
    u-c₄ = begin
      L u • c₄                                  ≈⟨ back _ c₄-tail ⟩
      L u • φ • Ex ↑ ↑ ↑                        ≈⟨ sym assoc ⟩
      (L u • φ) • Ex ↑ ↑ ↑                      ≈⟨ front _ u-φ ⟩
      (φ • P₀₃ u) • Ex ↑ ↑ ↑                    ≈⟨ assoc ⟩
      φ • P₀₃ u • Ex ↑ ↑ ↑                      ≈⟨ back _ (sym (cancelˡ _ Ex₃²)) ⟩
      φ • Ex ↑ ↑ ↑ • Ex ↑ ↑ ↑ • P₀₃ u • Ex ↑ ↑ ↑  ≈⟨ sym assoc ⟩
      (φ • Ex ↑ ↑ ↑) • S₃₄.⟪ P₀₃ u ⟫            ≈⟨ front _ (sym c₄-tail) ⟩
      c₄ • S₃₄.⟪ P₀₃ u ⟫ ∎

    Φ-u : Φ (S₃₄.⟪ P₀₃ u ⟫) ≈ P₂₃ u ↑
    Φ-u = begin
      S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ S₃₄.⟪ P₀₃ u ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (conj-swap far₀₃ (P₀₃ u))) ⟩
      S₂₃.⟪ S₁₂.⟪ S₃₄.⟪ S₀₁.⟪ P₀₃ u ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (S₃₄.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ (P₁₃ u)))) ⟩
      S₂₃.⟪ S₁₂.⟪ S₃₄.⟪ P₁₃ u ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (conj-swap far₁₃ (P₁₃ u)) ⟩
      S₂₃.⟪ S₃₄.⟪ S₁₂.⟪ P₁₃ u ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₃₄.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ (P₂₃ u))) ⟩
      S₂₃.⟪ S₃₄.⟪ P₂₃ u ⟫ ⟫
        ≈⟨ u-up ⟩
      P₂₃ u ↑ ∎

------------------------------------------------------------------------
-- (262) on the wires 0–3

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  private
    W₅ = Circuit (₁₊ (₄₊ n))

    PP₃₄ : W₅
    PP₃₄ = PP₂₃ {n} ↑

    PP-P : PP₀₁ • P ≈ P • PP₃₄
    PP-P = pair-P PP (L-sem (Ex • PP • Ex) PP Eq.refl)
      (lemma-cong↑ (U₃ (Ex ↓ • (Ex ↑ • PP ↓ • Ex ↑) • Ex ↓)) (U₃ (PP ↑))
                   (U₃-sem (Ex ↓ • (Ex ↑ • PP ↓ • Ex ↑) • Ex ↓) (PP ↑) Eq.refl))

    -- The rotation of wire 3 from the wires 0 1 2.
    e₃ : PP₃₄ • Φ ZX₃ ≈ Φ XZ₃ • PP₃₄
    e₃ = transport₂ Γ P-cancel PP-P
           (F-P (λ m → ZX₃ {m}) (λ m → Eq.refl)) (F-P (λ m → XZ₃ {m}) (λ m → Eq.refl)) eq262

    -- Back under the three lower swaps.
    Ψ : W₅ → W₅
    Ψ w = S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ w ⟫ ⟫ ⟫

    Ψ-cong : ∀ {x y : W₅} → x ≈ y → Ψ x ≈ Ψ y
    Ψ-cong e = S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong e))

    Ψ-• : (x y : W₅) → Ψ (x • y) ≈ Ψ x • Ψ y
    Ψ-• x y = trans (S₀₁.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-• x y)) (S₁₂.⟪⟫-• _ _)))
                    (S₀₁.⟪⟫-• _ _)

    Ψ-Φ : (F : W₅) → Ψ (Φ F) ≈ F
    Ψ-Φ F = trans (S₀₁.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ S₀₁.⟪ F ⟫ ⟫)))
                                      (S₁₂.⟪⟫-⟪⟫ (S₀₁.⟪ F ⟫))))
                  (S₀₁.⟪⟫-⟪⟫ F)

    -- P ⊗ P on the wires 0 4, in both spellings.
    Ψ-PP : Ψ PP₃₄ ≈ PP₀₄
    Ψ-PP = sym (begin
      S₃₄.⟪ S₀₁.⟪ S₁₂.⟪ PP₂₃ ⟫ ⟫ ⟫
        ≈⟨ sym (conj-swap far₀₃ (S₁₂.⟪ PP₂₃ ⟫)) ⟩
      S₀₁.⟪ S₃₄.⟪ S₁₂.⟪ PP₂₃ ⟫ ⟫ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (sym (conj-swap far₁₃ PP₂₃)) ⟩
      S₀₁.⟪ S₁₂.⟪ S₃₄.⟪ PP₂₃ ⟫ ⟫ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong
             (lemma-cong↑ (Ex ↑ ↑ • PP ↑ • Ex ↑ ↑) (Ex ↑ • PP ↑ ↑ • Ex ↑)
               (lemma-cong↑ (Ex ↑ • PP ↓ • Ex ↑) (Ex ↓ • PP ↑ • Ex ↓) (O-L PP)))) ⟩
      S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ PP₃₄ ⟫ ⟫ ⟫ ∎)

  PP₀₄² : PP₀₄ • PP₀₄ ≈ ε
  PP₀₄² = S₃₄.⟪⟫-invol PP₀₃²

  -- (262): P ⊗ P on the wires 0 4 turns the rotation of wire 0 over.
  PP₀₄-ZX₃ : PP₀₄ • ZX₃ ≈ XZ₃ • PP₀₄
  PP₀₄-ZX₃ = begin
    PP₀₄ • ZX₃                  ≈⟨ sym (cong Ψ-PP (Ψ-Φ ZX₃)) ⟩
    Ψ PP₃₄ • Ψ (Φ ZX₃)          ≈⟨ sym (Ψ-• PP₃₄ (Φ ZX₃)) ⟩
    Ψ (PP₃₄ • Φ ZX₃)            ≈⟨ Ψ-cong e₃ ⟩
    Ψ (Φ XZ₃ • PP₃₄)            ≈⟨ Ψ-• (Φ XZ₃) PP₃₄ ⟩
    Ψ (Φ XZ₃) • Ψ PP₃₄          ≈⟨ cong (Ψ-Φ XZ₃) Ψ-PP ⟩
    XZ₃ • PP₀₄ ∎

  PP₀₄-rot : ∀ b → PP₀₄ • rot b ≈ rot (not b) • PP₀₄
  PP₀₄-rot true  = PP₀₄-ZX₃
  PP₀₄-rot false = flip-pass Γ PP₀₄² PP₀₄-ZX₃

  ----------------------------------------------------------------------
  -- White controls: X on the wires 1, 2, 3 passes P ⊗ P on the wires 0 4


  private
    N₁-PP₀₄ : N₁.⟪ PP₀₄ ⟫ ≈ PP₀₄
    N₁-PP₀₄ = trans (conj-swap X₁-Ex₃₄ PP₀₃)
                    (S₃₄.⟪⟫-cong (N₁.⟪⟫-fix (sym (P₀₃-U PP (X ↓)))))

    N₂-PP₀₄ : N₂.⟪ PP₀₄ ⟫ ≈ PP₀₄
    N₂-PP₀₄ = trans (conj-swap X₂-Ex₃₄ PP₀₃)
                    (S₃₄.⟪⟫-cong (N₂.⟪⟫-fix (sym (P₀₃-U PP (X ↑)))))

    N₃-PP₀₄ : N₃.⟪ PP₀₄ ⟫ ≈ PP₀₄
    N₃-PP₀₄ = X₃-S₃₄ (sym (L₄-top (P₀₃ PP) X))

    via-N₁ : ∀ {w w′ : W₅} → PP₀₄ • w ≈ w′ • PP₀₄ → PP₀₄ • N₁.⟪ w ⟫ ≈ N₁.⟪ w′ ⟫ • PP₀₄
    via-N₁ e = N₁.⟪⟫-≈ e (N₁.⟪⟫-•₂ N₁-PP₀₄ refl) (N₁.⟪⟫-•₂ refl N₁-PP₀₄)

    via-N₂ : ∀ {w w′ : W₅} → PP₀₄ • w ≈ w′ • PP₀₄ → PP₀₄ • N₂.⟪ w ⟫ ≈ N₂.⟪ w′ ⟫ • PP₀₄
    via-N₂ e = N₂.⟪⟫-≈ e (N₂.⟪⟫-•₂ N₂-PP₀₄ refl) (N₂.⟪⟫-•₂ refl N₂-PP₀₄)

    via-N₃ : ∀ {w w′ : W₅} → PP₀₄ • w ≈ w′ • PP₀₄ → PP₀₄ • N₃.⟪ w ⟫ ≈ N₃.⟪ w′ ⟫ • PP₀₄
    via-N₃ e = N₃.⟪⟫-≈ e (N₃.⟪⟫-•₂ N₃-PP₀₄ refl) (N₃.⟪⟫-•₂ refl N₃-PP₀₄)

    PP₀₄-N₁ᵇ : ∀ β b → PP₀₄ • N₁ᵇ β (rot b) ≈ N₁ᵇ β (rot (not b)) • PP₀₄
    PP₀₄-N₁ᵇ true  b = PP₀₄-rot b
    PP₀₄-N₁ᵇ false b = via-N₁ (PP₀₄-rot b)

    PP₀₄-N₂ᵇ : ∀ α b → PP₀₄ • N₂ᵇ α (rot b) ≈ N₂ᵇ α (rot (not b)) • PP₀₄
    PP₀₄-N₂ᵇ true  b = PP₀₄-rot b
    PP₀₄-N₂ᵇ false b = via-N₂ (PP₀₄-rot b)

  -- The second gate of (245), and the rotation with the coloured control
  -- on wire 2.
  PP₀₄-S : ∀ β b → PP₀₄ • S₂₄₅ β b ≈ S₂₄₅ β (not b) • PP₀₄
  PP₀₄-S β b = via-N₃ (PP₀₄-N₁ᵇ β b)

  PP₀₄-V : ∀ α b → PP₀₄ • V₂₆₃ α b ≈ V₂₆₃ α (not b) • PP₀₄
  PP₀₄-V α b = via-N₃ (PP₀₄-N₂ᵇ α b)

  ----------------------------------------------------------------------
  -- The target on wire 2

  private
    θ-PP : S₁₂.⟪ S₀₁.⟪ PP₀₄ ⟫ ⟫ ≈ PP₂₄
    θ-PP = begin
      S₁₂.⟪ S₀₁.⟪ S₃₄.⟪ PP₀₃ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (conj-swap far₀₃ PP₀₃) ⟩
      S₁₂.⟪ S₃₄.⟪ S₀₁.⟪ PP₀₃ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₃₄.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ (P₁₃ PP))) ⟩
      S₁₂.⟪ S₃₄.⟪ P₁₃ PP ⟫ ⟫
        ≈⟨ conj-swap far₁₃ (P₁₃ PP) ⟩
      S₃₄.⟪ S₁₂.⟪ P₁₃ PP ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ (P₂₃ PP)) ⟩
      S₃₄.⟪ PP₂₃ ⟫ ∎

  PP₂₄-J : ∀ α b → PP₂₄ • J₂₆₃ α b ≈ J₂₆₃ α (not b) • PP₂₄
  PP₂₄-J α b = trans (front _ (sym θ-PP)) (trans e₂ (back _ θ-PP))
    where
    e₁ : S₀₁.⟪ PP₀₄ ⟫ • S₀₁.⟪ V₂₆₃ α b ⟫ ≈ S₀₁.⟪ V₂₆₃ α (not b) ⟫ • S₀₁.⟪ PP₀₄ ⟫
    e₁ = S₀₁.⟪⟫-≈ (PP₀₄-V α b) (S₀₁.⟪⟫-• PP₀₄ (V₂₆₃ α b)) (S₀₁.⟪⟫-• (V₂₆₃ α (not b)) PP₀₄)
    e₂ : S₁₂.⟪ S₀₁.⟪ PP₀₄ ⟫ ⟫ • J₂₆₃ α b ≈ J₂₆₃ α (not b) • S₁₂.⟪ S₀₁.⟪ PP₀₄ ⟫ ⟫
    e₂ = S₁₂.⟪⟫-≈ e₁ (S₁₂.⟪⟫-• _ _) (S₁₂.⟪⟫-• _ _)
