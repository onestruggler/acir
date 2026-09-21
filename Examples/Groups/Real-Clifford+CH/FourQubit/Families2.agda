------------------------------------------------------------------------
-- Presentations of groups
--
-- Two triply controlled rotations of wire 0 whose controls on wire 2
-- differ in colour (Clément, Lemma D.5, Equation (241))
--
-- The controls on the wires 1 and 3 have any colours, and each rotation
-- is ZX or XZ: sixty-four cases.  X on a wire that controls both gates
-- exchanges the colours of both there, so the first gate may be taken
-- black (`step-β`, `eq241`); ZX and XZ are inverse to each other, so both
-- may be taken ZX (`all-rot`).  Four cases are left, the colours of the
-- second gate on the wires 3 and 1:
--
--   black, black   the merge (221) holds in both orders
--   white, black   by the merge on wire 3, (223), the second gate is the
--                  doubly controlled ZX, white on wire 2, times a gate of
--                  the first case; the XZ in its form B a B a passes the
--                  former by `pass-pqpq` — B passes it, (176), and a
--                  turns it over
--   black, white   the same under (1 3)
--   white, white   as the second, with both controls of the doubly
--                  controlled ZX white: B still passes it, and a does by
--                  one three-wire evaluation (Evals241)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Families2
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; CH² ; S-X↓ ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals241 complete₂ complete₃
  using (ev-CH-°°CCZX)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq156)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq176)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (merge₀ ; merge₀′ ; eq223)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; °CCZX ; °CCXZ ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- Controls of either colour

-- A control on wire 1 or 3, black (true) or white.
N₁ᵇ N₃ᵇ : Bool → Circuit (₄₊ n) → Circuit (₄₊ n)
N₁ᵇ true  w = w
N₁ᵇ false w = N₁.⟪ w ⟫
N₃ᵇ true  w = w
N₃ᵇ false w = N₃.⟪ w ⟫

-- (−1)ᵃ XZ, triply controlled, on wire 0.
rot : Bool → Circuit (₄₊ n)
rot false = XZ₃
rot true  = ZX₃

-- The two gates of (241).
A₂₄₁ C₂₄₁ : Bool → Bool → Bool → Circuit (₄₊ n)
A₂₄₁ α β a = N₃ᵇ α (N₁ᵇ β (rot a))
C₂₄₁ γ δ b = N₃ᵇ γ (N₁ᵇ δ (N₂.⟪ rot b ⟫))

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    a B °b °Z °Z′ : Circuit (₄₊ n)
    a   = CH ↓
    B   = box₃′
    °b  = °CZ₂₀
    °Z  = N₂.⟪ ZX₃ ⟫
    °Z′ = N₂.⟪ XZ₃ ⟫

    --------------------------------------------------------------------
    -- X on different wires

    X₁-X₃ : X ↑ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↑
    X₁-X₃ = lemma-cong↑ (X ↓ • X ↑ ↑) (X ↑ ↑ • X ↓) (comm-↓↑ X (X ↑))

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    N₁-N₃ : (w : Circuit (₄₊ n)) → N₁.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₃.⟪ N₁.⟪ w ⟫ ⟫
    N₁-N₃ = conj-swap X₁-X₃

    --------------------------------------------------------------------
    -- Inverses

    °Z°Z′ : °Z • °Z′ ≈ ε
    °Z°Z′ = trans (sym (N₂.⟪⟫-• ZX₃ XZ₃)) (trans (N₂.⟪⟫-cong eq208′) N₂.⟪⟫-ε)

    °Z′°Z : °Z′ • °Z ≈ ε
    °Z′°Z = trans (sym (N₂.⟪⟫-• XZ₃ ZX₃)) (trans (N₂.⟪⟫-cong eq208) N₂.⟪⟫-ε)

    N₁ᵇ-inv : ∀ δ {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₁ᵇ δ u • N₁ᵇ δ v ≈ ε
    N₁ᵇ-inv true  e = e
    N₁ᵇ-inv false {u} {v} e = trans (sym (N₁.⟪⟫-• u v)) (trans (N₁.⟪⟫-cong e) N₁.⟪⟫-ε)

    N₃ᵇ-inv : ∀ γ {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₃ᵇ γ u • N₃ᵇ γ v ≈ ε
    N₃ᵇ-inv true  e = e
    N₃ᵇ-inv false {u} {v} e = trans (sym (N₃.⟪⟫-• u v)) (trans (N₃.⟪⟫-cong e) N₃.⟪⟫-ε)

    C-inv : ∀ γ δ → C₂₄₁ γ δ true • C₂₄₁ γ δ false ≈ ε
    C-inv γ δ = N₃ᵇ-inv γ (N₁ᵇ-inv δ °Z°Z′)

    C-inv′ : ∀ γ δ → C₂₄₁ γ δ false • C₂₄₁ γ δ true ≈ ε
    C-inv′ γ δ = N₃ᵇ-inv γ (N₁ᵇ-inv δ °Z′°Z)

    -- w passes y, so its inverse does.
    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    --------------------------------------------------------------------
    -- Black, black: the merge in both orders

    Z-°Z : ZX₃ • °Z ≈ °Z • ZX₃
    Z-°Z = trans merge₀′ (sym merge₀)

    Z-°Z′ : ZX₃ • °Z′ ≈ °Z′ • ZX₃
    Z-°Z′ = comm-inv °Z°Z′ °Z′°Z Z-°Z

    --------------------------------------------------------------------
    -- The doubly controlled ZX, white on wire 2

    N₂-a : N₂.⟪ a ⟫ ≈ a
    N₂-a = N₂.⟪⟫-fix (sym (L-comm CH X))

    °W-form : °CCZX ≈ a • °b • a • °b
    °W-form = N₂.⟪⟫-•₄ N₂-a refl N₂-a refl

    °V-form : °CCXZ ≈ °b • a • °b • a
    °V-form = N₂.⟪⟫-•₄ refl N₂-a refl N₂-a

    °W°V : °CCZX • °CCXZ ≈ ε
    °W°V = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)

    °V°W : °CCXZ • °CCZX ≈ ε
    °V°W = trans (sym (N₂.⟪⟫-• CCXZ CCZX)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)

    -- B passes it, (176); a turns it over.
    B-°V : B • °CCXZ ≈ °CCXZ • B
    B-°V = sym eq176

    B-°W : B • °CCZX ≈ °CCZX • B
    B-°W = comm-inv °V°W °W°V B-°V

    a-°V : a • °CCXZ ≈ °CCZX • a
    a-°V = begin
      a • °CCXZ                     ≈⟨ back _ °V-form ⟩
      a • (°b • a • °b • a)         ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (a • °b • a • °b) • a         ≈⟨ front _ (sym °W-form) ⟩
      °CCZX • a ∎

    a-°W : a • °CCZX ≈ °CCXZ • a
    a-°W = sym (conj-comm CH² (trans (sym assoc) (trans (front _ a-°V) (cancelʳ _ CH²))))

    XZ₃-°W : XZ₃ • °CCZX ≈ °CCZX • XZ₃
    XZ₃-°W = pass-pqpq B-°W B-°V a-°W a-°V

    ZX₃-°W : ZX₃ • °CCZX ≈ °CCZX • ZX₃
    ZX₃-°W = inv-row eq208 eq208′ XZ₃-°W

    --------------------------------------------------------------------
    -- White on wire 3: the merge (223), white on wire 2

    °merge₃ : N₃.⟪ °Z ⟫ • °Z ≈ °CCZX
    °merge₃ = trans (front _ (sym (N₂-N₃ ZX₃))) (N₂.⟪⟫-≈ eq223 (N₂.⟪⟫-• (N₃.⟪ ZX₃ ⟫) ZX₃) refl)

    N₃°Z-form : N₃.⟪ °Z ⟫ ≈ °CCZX • °Z′
    N₃°Z-form = begin
      N₃.⟪ °Z ⟫                     ≈⟨ sym right-unit ⟩
      N₃.⟪ °Z ⟫ • ε                 ≈⟨ back _ (sym °Z°Z′) ⟩
      N₃.⟪ °Z ⟫ • °Z • °Z′          ≈⟨ sym assoc ⟩
      (N₃.⟪ °Z ⟫ • °Z) • °Z′        ≈⟨ front _ °merge₃ ⟩
      °CCZX • °Z′ ∎

    Z-N₃°Z : ZX₃ • N₃.⟪ °Z ⟫ ≈ N₃.⟪ °Z ⟫ • ZX₃
    Z-N₃°Z = begin
      ZX₃ • N₃.⟪ °Z ⟫           ≈⟨ back _ N₃°Z-form ⟩
      ZX₃ • (°CCZX • °Z′)       ≈⟨ comm-• ZX₃-°W Z-°Z′ ⟩
      (°CCZX • °Z′) • ZX₃       ≈⟨ front _ (sym N₃°Z-form) ⟩
      N₃.⟪ °Z ⟫ • ZX₃ ∎

    --------------------------------------------------------------------
    -- White on wire 1: the same under (1 3)

    T₁₃-ZX₃ : T₁₃.⟪ ZX₃ ⟫ ≈ ZX₃
    T₁₃-ZX₃ = T₁₃-via S₂₃-ZX₃ S₁₂-ZX₃ S₂₃-ZX₃

    Z-N₁°Z : ZX₃ • N₁.⟪ °Z ⟫ ≈ N₁.⟪ °Z ⟫ • ZX₃
    Z-N₁°Z = T₁₃.⟪⟫-≈ Z-N₃°Z (T₁₃.⟪⟫-•₂ T₁₃-ZX₃ m) (T₁₃.⟪⟫-•₂ m T₁₃-ZX₃)
      where
      m : T₁₃.⟪ N₃.⟪ °Z ⟫ ⟫ ≈ N₁.⟪ °Z ⟫
      m = T₁₃-N₃ (T₁₃-N₂ T₁₃-ZX₃)

    Z-N₁°Z′ : ZX₃ • N₁.⟪ °Z′ ⟫ ≈ N₁.⟪ °Z′ ⟫ • ZX₃
    Z-N₁°Z′ = comm-inv (N₁ᵇ-inv false °Z°Z′) (N₁ᵇ-inv false °Z′°Z) Z-N₁°Z

    --------------------------------------------------------------------
    -- White on both

    X₁-B : X ↑ • B ≈ B • X ↑
    X₁-B = S₀₁.⟪⟫-≈ eq156 (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓)

    B-N₁°W : B • N₁.⟪ °CCZX ⟫ ≈ N₁.⟪ °CCZX ⟫ • B
    B-N₁°W = N₁.⟪⟫-≈ B-°W (N₁.⟪⟫-•₂ (N₁.⟪⟫-fix X₁-B) refl) (N₁.⟪⟫-•₂ refl (N₁.⟪⟫-fix X₁-B))

    a-N₁°W : a • N₁.⟪ °CCZX ⟫ ≈ N₁.⟪ °CCZX ⟫ • a
    a-N₁°W = L₃-comm-ev ev-CH-°°CCZX

    XZ₃-N₁°W : XZ₃ • N₁.⟪ °CCZX ⟫ ≈ N₁.⟪ °CCZX ⟫ • XZ₃
    XZ₃-N₁°W = sym (comm-abab (sym B-N₁°W) (sym a-N₁°W))

    ZX₃-N₁°W : ZX₃ • N₁.⟪ °CCZX ⟫ ≈ N₁.⟪ °CCZX ⟫ • ZX₃
    ZX₃-N₁°W = inv-row eq208 eq208′ XZ₃-N₁°W

    N₃N₁°Z-form : N₃.⟪ N₁.⟪ °Z ⟫ ⟫ ≈ N₁.⟪ °CCZX ⟫ • N₁.⟪ °Z′ ⟫
    N₃N₁°Z-form = begin
      N₃.⟪ N₁.⟪ °Z ⟫ ⟫                   ≈⟨ sym (N₁-N₃ °Z) ⟩
      N₁.⟪ N₃.⟪ °Z ⟫ ⟫                   ≈⟨ N₁.⟪⟫-cong N₃°Z-form ⟩
      N₁.⟪ °CCZX • °Z′ ⟫                 ≈⟨ N₁.⟪⟫-• °CCZX °Z′ ⟩
      N₁.⟪ °CCZX ⟫ • N₁.⟪ °Z′ ⟫ ∎

    Z-N₃N₁°Z : ZX₃ • N₃.⟪ N₁.⟪ °Z ⟫ ⟫ ≈ N₃.⟪ N₁.⟪ °Z ⟫ ⟫ • ZX₃
    Z-N₃N₁°Z = begin
      ZX₃ • N₃.⟪ N₁.⟪ °Z ⟫ ⟫                    ≈⟨ back _ N₃N₁°Z-form ⟩
      ZX₃ • (N₁.⟪ °CCZX ⟫ • N₁.⟪ °Z′ ⟫)         ≈⟨ comm-• ZX₃-N₁°W Z-N₁°Z′ ⟩
      (N₁.⟪ °CCZX ⟫ • N₁.⟪ °Z′ ⟫) • ZX₃         ≈⟨ front _ (sym N₃N₁°Z-form) ⟩
      N₃.⟪ N₁.⟪ °Z ⟫ ⟫ • ZX₃ ∎

    --------------------------------------------------------------------
    -- The first gate black

    core-ZX : ∀ γ δ → ZX₃ • C₂₄₁ γ δ true ≈ C₂₄₁ γ δ true • ZX₃
    core-ZX true  true  = Z-°Z
    core-ZX false true  = Z-N₃°Z
    core-ZX true  false = Z-N₁°Z
    core-ZX false false = Z-N₃N₁°Z

    all-rot : ∀ {g : Circuit (₄₊ n)} → ZX₃ • g ≈ g • ZX₃ → ∀ a → rot a • g ≈ g • rot a
    all-rot e true  = e
    all-rot e false = inv-row eq208′ eq208 e

    core : ∀ γ δ a b → rot a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • rot a
    core γ δ a true  = all-rot (core-ZX γ δ) a
    core γ δ a false = all-rot (comm-inv (C-inv γ δ) (C-inv′ γ δ) (core-ZX γ δ)) a

    --------------------------------------------------------------------
    -- X on a wire that controls both gates

    flip₁ : ∀ γ δ (w : Circuit (₄₊ n)) → N₁.⟪ N₃ᵇ γ (N₁ᵇ (not δ) w) ⟫ ≈ N₃ᵇ γ (N₁ᵇ δ w)
    flip₁ true  true  w = N₁.⟪⟫-⟪⟫ w
    flip₁ true  false w = refl
    flip₁ false true  w = trans (N₁-N₃ (N₁.⟪ w ⟫)) (N₃.⟪⟫-cong (N₁.⟪⟫-⟪⟫ w))
    flip₁ false false w = N₁-N₃ w

    flip₃ : ∀ γ (w : Circuit (₄₊ n)) → N₃.⟪ N₃ᵇ (not γ) w ⟫ ≈ N₃ᵇ γ w
    flip₃ true  w = N₃.⟪⟫-⟪⟫ w
    flip₃ false w = refl

    step-β : ∀ β γ δ a b → N₁ᵇ β (rot a) • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • N₁ᵇ β (rot a)
    step-β true  γ δ a b = core γ δ a b
    step-β false γ δ a b = N₁.⟪⟫-≈ (core γ (not δ) a b)
      (N₁.⟪⟫-•₂ refl (flip₁ γ δ (N₂.⟪ rot b ⟫)))
      (N₁.⟪⟫-•₂ (flip₁ γ δ (N₂.⟪ rot b ⟫)) refl)

  -- The second gate's inverse.
  C₂₄₁-inv : ∀ γ δ → C₂₄₁ γ δ true • C₂₄₁ γ δ false ≈ ε
  C₂₄₁-inv = C-inv

  C₂₄₁-inv′ : ∀ γ δ → C₂₄₁ γ δ false • C₂₄₁ γ δ true ≈ ε
  C₂₄₁-inv′ = C-inv′

  -- The merge on wire 3 of the gate white on wire 2, and X on the wires
  -- 1 and 3, for later use.
  °merge-on-3 : N₃.⟪ N₂.⟪ ZX₃ ⟫ ⟫ • N₂.⟪ ZX₃ ⟫ ≈ °CCZX
  °merge-on-3 = °merge₃

  N₁-N₃-swap : (w : Circuit (₄₊ n)) → N₁.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₃.⟪ N₁.⟪ w ⟫ ⟫
  N₁-N₃-swap = N₁-N₃

  -- (241)
  eq241 : ∀ α β γ δ a b → A₂₄₁ α β a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • A₂₄₁ α β a
  eq241 true  β γ δ a b = step-β β γ δ a b
  eq241 false β γ δ a b = N₃.⟪⟫-≈ (step-β β (not γ) δ a b)
    (N₃.⟪⟫-•₂ refl (flip₃ γ (N₁ᵇ δ (N₂.⟪ rot b ⟫))))
    (N₃.⟪⟫-•₂ (flip₃ γ (N₁ᵇ δ (N₂.⟪ rot b ⟫))) refl)
