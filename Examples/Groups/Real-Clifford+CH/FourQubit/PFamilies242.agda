------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P against one of the other
-- colour, crossed (Clément, Lemma D.5, Equation (242))
--
-- The first gate is that of (240) between P ⊗ P on the wires 0 1, the
-- second that of (240).  As for (243): X on wire 3 and inverses reduce
-- the colours and signs; a white control of the first gate on wire 1
-- adds a doubly controlled XZ, the merge of two gates of (240).  With the
-- first gate black, G′ P G′ P:
--
--   the second gate black on wire 0: it is °G′ °B °G′ °B with °B the box
--     on wire 0, white on wire 2 and perhaps on wire 3, and the letters
--     pass each other by (201), (182), (204), (194), (195);
--   white on wire 0: by the merge on wire 0 it is the doubly controlled
--     rotation of wire 1 from the wires 2 3, white on wire 2, times a gate
--     of the first kind; that rotation is the merge of two gates of (240)
--     and is turned over between P ⊗ P.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies242
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (CCZX₂₃ ; CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; °°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (eq182)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq194 ; eq195)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; eq201)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq204)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (K ; K′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families complete₂ complete₃
  using (R₁ ; R₁′ ; R₁-inv ; R₁-inv′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃
  using (module N₀ ; N₀ᵇ ; rot₁ ; D₂₄₀ ; D₂₄₀-inv ; D₂₄₀-inv′ ; eq240)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃
  using (N₃-S₀₁ΛH₂′ ; N₃-S₀₁°ΛH₂′ ; °ZX₃-as-GBGB ; °merge-on-1 ; PP-R₁′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    G′ °G′ P °Z : Circuit (₄₊ n)
    G′  = S₀₁.⟪ ΛH₂′ ⟫
    °G′ = S₀₁.⟪ °ΛH₂′ ⟫
    P   = ΛH₀₁
    °Z  = N₂.⟪ ZX₃ ⟫

    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    words : ∀ {x₁ x₂ y₁ y₂ : Circuit (₄₊ n)} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (x₁ • x₂ • x₁ • x₂) • (y₁ • y₂ • y₁ • y₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
    words e₁₁ e₁₂ e₂₁ e₂₂ =
      sym (comm-abab (sym (comm-abab e₁₁ e₁₂)) (sym (comm-abab e₂₁ e₂₂)))

    --------------------------------------------------------------------
    -- The second gate black on wire 0

    K-form₄ : K ≈ °G′ • °box₃ • °G′ • °box₃
    K-form₄ = trans (S₀₁.⟪⟫-cong °ZX₃-as-GBGB)
                    (S₀₁.⟪⟫-•₄ refl (S₀₁.⟪⟫-⟪⟫ °box₃) refl (S₀₁.⟪⟫-⟪⟫ °box₃))

    N₃K-form : N₃.⟪ K ⟫ ≈ °G′ • °°box₃ • °G′ • °°box₃
    N₃K-form = trans (N₃.⟪⟫-cong K-form₄) (N₃.⟪⟫-•₄ N₃-S₀₁°ΛH₂′ refl N₃-S₀₁°ΛH₂′ refl)

    G′-°°box₃ : G′ • °°box₃ ≈ °°box₃ • G′
    G′-°°box₃ = N₃.⟪⟫-≈ eq182 (N₃.⟪⟫-•₂ N₃-S₀₁ΛH₂′ refl) (N₃.⟪⟫-•₂ refl N₃-S₀₁ΛH₂′)

    base₁ : ∀ γ → Aᴾ true true true • D₂₄₀ γ true true ≈ D₂₄₀ γ true true • Aᴾ true true true
    base₁ true = begin
      Aᴾ true true true • K
        ≈⟨ cong Aᴾ-form K-form₄ ⟩
      (G′ • P • G′ • P) • (°G′ • °box₃ • °G′ • °box₃)
        ≈⟨ words eq201 eq182 eq204 eq194 ⟩
      (°G′ • °box₃ • °G′ • °box₃) • (G′ • P • G′ • P)
        ≈⟨ sym (cong K-form₄ Aᴾ-form) ⟩
      K • Aᴾ true true true ∎
    base₁ false = begin
      Aᴾ true true true • N₃.⟪ K ⟫
        ≈⟨ cong Aᴾ-form N₃K-form ⟩
      (G′ • P • G′ • P) • (°G′ • °°box₃ • °G′ • °°box₃)
        ≈⟨ words eq201 G′-°°box₃ eq204 eq195 ⟩
      (°G′ • °°box₃ • °G′ • °°box₃) • (G′ • P • G′ • P)
        ≈⟨ sym (cong N₃K-form Aᴾ-form) ⟩
      N₃.⟪ K ⟫ • Aᴾ true true true ∎

    base₁′ : ∀ γ → Aᴾ true true true • D₂₄₀ γ true false ≈ D₂₄₀ γ true false • Aᴾ true true true
    base₁′ γ = comm-inv (D₂₄₀-inv γ true) (D₂₄₀-inv′ γ true) (base₁ γ)

    --------------------------------------------------------------------
    -- The second gate white on wire 0

    -- The doubly controlled rotation of wire 1 from the wires 2 3, white
    -- on wire 2, and its inverse.
    Q Q′ : Bool → Circuit (₄₊ n)
    Q  γ = N₃ᵇ γ (S₀₁.⟪ R₁ ⟫)
    Q′ γ = N₃ᵇ γ (S₀₁.⟪ R₁′ ⟫)

    N₃ᵇ-inv : ∀ γ {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₃ᵇ γ u • N₃ᵇ γ v ≈ ε
    N₃ᵇ-inv true  e = e
    N₃ᵇ-inv false {u} {v} e = trans (sym (N₃.⟪⟫-• u v)) (trans (N₃.⟪⟫-cong e) N₃.⟪⟫-ε)

    QQ′ : ∀ γ → Q γ • Q′ γ ≈ ε
    QQ′ γ = N₃ᵇ-inv γ (trans (sym (S₀₁.⟪⟫-• R₁ R₁′)) (trans (S₀₁.⟪⟫-cong R₁-inv) S₀₁.⟪⟫-ε))

    Q′Q : ∀ γ → Q′ γ • Q γ ≈ ε
    Q′Q γ = N₃ᵇ-inv γ (trans (sym (S₀₁.⟪⟫-• R₁′ R₁)) (trans (S₀₁.⟪⟫-cong R₁-inv′) S₀₁.⟪⟫-ε))

    -- The merge on wire 0: (the lower swap exchanges X on the wires 0, 1).
    D-merge : ∀ γ → D₂₄₀ γ false true • D₂₄₀ γ true true ≈ Q γ
    D-merge true  = S₀₁.⟪⟫-≈ °merge-on-1 (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-•₃ S-X↑ refl S-X↑) refl) refl
    D-merge false = trans (sym (N₃.⟪⟫-• (N₀.⟪ K ⟫) K)) (N₃.⟪⟫-cong (D-merge true))

    D-white : ∀ γ → D₂₄₀ γ false true ≈ Q γ • D₂₄₀ γ true false
    D-white γ = begin
      D₂₄₀ γ false true
        ≈⟨ sym right-unit ⟩
      D₂₄₀ γ false true • ε
        ≈⟨ back _ (sym (D₂₄₀-inv γ true)) ⟩
      D₂₄₀ γ false true • D₂₄₀ γ true true • D₂₄₀ γ true false
        ≈⟨ sym assoc ⟩
      (D₂₄₀ γ false true • D₂₄₀ γ true true) • D₂₄₀ γ true false
        ≈⟨ front _ (D-merge γ) ⟩
      Q γ • D₂₄₀ γ true false ∎

    -- The rotation of wire 0 passes it, (240) twice …
    Z-Q : ∀ γ → ZX₃ • Q γ ≈ Q γ • ZX₃
    Z-Q γ = begin
      ZX₃ • Q γ
        ≈⟨ back _ (sym (D-merge γ)) ⟩
      ZX₃ • (D₂₄₀ γ false true • D₂₄₀ γ true true)
        ≈⟨ comm-• (eq240 true true γ false true true) (eq240 true true γ true true true) ⟩
      (D₂₄₀ γ false true • D₂₄₀ γ true true) • ZX₃
        ≈⟨ front _ (D-merge γ) ⟩
      Q γ • ZX₃ ∎

    Z-Q′ : ∀ γ → ZX₃ • Q′ γ ≈ Q′ γ • ZX₃
    Z-Q′ γ = comm-inv (QQ′ γ) (Q′Q γ) (Z-Q γ)

    -- … and between P ⊗ P it is turned over.
    PP-Ex : PP₀₁ • Ex ↓ ≈ Ex ↓ • PP₀₁
    PP-Ex = L-sem (PP • Ex) (Ex • PP) Eq.refl

    X₃-PP : X ↑ ↑ ↑ • PP₀₁ ≈ PP₀₁ • X ↑ ↑ ↑
    X₃-PP = N₃.⟪⟫-comm N₃-PP₀₁

    Aj-Q′ : ∀ γ → Aj.⟪ Q′ γ ⟫ ≈ Q γ
    Aj-Q′ true  = trans (conj-swap PP-Ex R₁′) (S₀₁.⟪⟫-cong PP-R₁′)
    Aj-Q′ false = trans (conj-swap (sym X₃-PP) (S₀₁.⟪ R₁′ ⟫)) (N₃.⟪⟫-cong (Aj-Q′ true))

    Aᴾ-Q : ∀ γ → Aᴾ true true true • Q γ ≈ Q γ • Aᴾ true true true
    Aᴾ-Q γ = Aj.⟪⟫-≈ (Z-Q′ γ) (Aj.⟪⟫-•₂ refl (Aj-Q′ γ)) (Aj.⟪⟫-•₂ (Aj-Q′ γ) refl)

    base₀ : ∀ γ → Aᴾ true true true • D₂₄₀ γ false true ≈ D₂₄₀ γ false true • Aᴾ true true true
    base₀ γ = begin
      Aᴾ true true true • D₂₄₀ γ false true
        ≈⟨ back _ (D-white γ) ⟩
      Aᴾ true true true • (Q γ • D₂₄₀ γ true false)
        ≈⟨ comm-• (Aᴾ-Q γ) (base₁′ γ) ⟩
      (Q γ • D₂₄₀ γ true false) • Aᴾ true true true
        ≈⟨ front _ (sym (D-white γ)) ⟩
      D₂₄₀ γ false true • Aᴾ true true true ∎

    --------------------------------------------------------------------
    -- The first gate black on the wires 1 and 3

    core-ZX : ∀ γ δ → Aᴾ true true true • D₂₄₀ γ δ true ≈ D₂₄₀ γ δ true • Aᴾ true true true
    core-ZX γ true  = base₁ γ
    core-ZX γ false = base₀ γ

    all-a : ∀ {g : Circuit (₄₊ n)} → Aᴾ true true true • g ≈ g • Aᴾ true true true →
            ∀ a → Aᴾ true true a • g ≈ g • Aᴾ true true a
    all-a e true  = e
    all-a e false = inv-row (Aᴾ-inv true true) (Aᴾ-inv′ true true) e

    black : ∀ γ δ a b → Aᴾ true true a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • Aᴾ true true a
    black γ δ a true  = all-a (core-ZX γ δ) a
    black γ δ a false = all-a (comm-inv (D₂₄₀-inv γ δ) (D₂₄₀-inv′ γ δ) (core-ZX γ δ)) a

    --------------------------------------------------------------------
    -- The first gate white on wire 1

    W₂₃-D : ∀ γ δ b → CCZX₂₃ • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • CCZX₂₃
    W₂₃-D γ δ b = begin
      CCZX₂₃ • D₂₄₀ γ δ b
        ≈⟨ front _ (sym merge₁) ⟩
      (N₁.⟪ ZX₃ ⟫ • ZX₃) • D₂₄₀ γ δ b
        ≈⟨ sym (comm-• (sym (eq240 true false γ δ true b)) (sym (eq240 true true γ δ true b))) ⟩
      D₂₄₀ γ δ b • (N₁.⟪ ZX₃ ⟫ • ZX₃)
        ≈⟨ back _ merge₁ ⟩
      D₂₄₀ γ δ b • CCZX₂₃ ∎

    W₂₃V₂₃ : CCZX₂₃ • CCXZ₂₃ ≈ ε
    W₂₃V₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCZX) (U₃ CCXZ)))
            (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCZX • CCXZ) ε eq117)) S₀₁.⟪⟫-ε)

    V₂₃W₂₃ : CCXZ₂₃ • CCZX₂₃ ≈ ε
    V₂₃W₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCXZ) (U₃ CCZX)))
            (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCXZ • CCZX) ε eq118)) S₀₁.⟪⟫-ε)

    V₂₃-D : ∀ γ δ b → CCXZ₂₃ • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • CCXZ₂₃
    V₂₃-D γ δ b = inv-row W₂₃V₂₃ V₂₃W₂₃ (W₂₃-D γ δ b)

    white-ZX : ∀ γ δ b → Aᴾ true false true • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • Aᴾ true false true
    white-ZX γ δ b = begin
      Aᴾ true false true • D₂₄₀ γ δ b
        ≈⟨ front _ Aᴾ-white ⟩
      (CCXZ₂₃ • Aᴾ true true false) • D₂₄₀ γ δ b
        ≈⟨ sym (comm-• (sym (V₂₃-D γ δ b)) (sym (black γ δ false b))) ⟩
      D₂₄₀ γ δ b • (CCXZ₂₃ • Aᴾ true true false)
        ≈⟨ back _ (sym Aᴾ-white) ⟩
      D₂₄₀ γ δ b • Aᴾ true false true ∎

    white : ∀ γ δ a b → Aᴾ true false a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • Aᴾ true false a
    white γ δ true  b = white-ZX γ δ b
    white γ δ false b = inv-row (Aᴾ-inv true false) (Aᴾ-inv′ true false) (white-ZX γ δ b)

    stage-β : ∀ β γ δ a b → Aᴾ true β a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • Aᴾ true β a
    stage-β true  = black
    stage-β false = white

    flip₃ : ∀ γ (w : Circuit (₄₊ n)) → N₃.⟪ N₃ᵇ (not γ) w ⟫ ≈ N₃ᵇ γ w
    flip₃ true  w = N₃.⟪⟫-⟪⟫ w
    flip₃ false w = refl

  -- (242)
  eq242 : ∀ α β γ δ a b → Aᴾ α β a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • Aᴾ α β a
  eq242 true  β γ δ a b = stage-β β γ δ a b
  eq242 false β γ δ a b = N₃.⟪⟫-≈ (stage-β β (not γ) δ a b)
    (N₃.⟪⟫-•₂ (N₃-Aᴾ β a) (flip₃ γ (N₀ᵇ δ (rot₁ b))))
    (N₃.⟪⟫-•₂ (flip₃ γ (N₀ᵇ δ (rot₁ b))) (N₃-Aᴾ β a))
