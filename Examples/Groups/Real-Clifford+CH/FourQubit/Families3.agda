------------------------------------------------------------------------
-- Presentations of groups
--
-- Two triply controlled rotations, crossed, whose controls on wire 2
-- differ in colour (Clément, Lemma D.5, Equation (240))
--
-- The first gate rotates wire 0, from the wires 1, 2, 3; the second
-- rotates wire 1, from the wires 0, 3 and, negatively, 2.  The other
-- controls have any colours and each rotation is ZX or XZ.  X on wire 3
-- exchanges the colours of both gates there; X on the target of one gate
-- exchanges the colour of the other there and turns the first over,
-- (238): so all controls but the second gate's on wire 3 may be taken
-- black (`stage₁`–`eq240`).  Then:
--
--   black   (216) one wire up: the first gate is P q P q with P the H gate
--           on the wires 0 1 and q the lower CZ — (212) under (1 3) —, q
--           exchanges the second gate K and its inverse as in (216), and
--           P passes K in its form °G′ c′ °G′ c′: the H gate by (204), the
--           CZ c′ because between P ⊗ P it is a CH onto a box wire
--   white   by the merge on wire 3, (223), the second gate is the doubly
--           controlled rotation of wire 1 times the inverse of K, and the
--           first passes that by (216) itself, mirrored
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Families3
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; S-X↓ ; S-X↑ ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq163)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (°ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₁² ; ΛH₀₁-PP ; S₀₁-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq204)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (K ; K′ ; K-as-GcGc ; K′-as-cGcG ; CZ↓-K ; CZ↓-K′ ; K-K′ ; eq216)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃
  using (eq238)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; °merge-on-3 ; N₁-N₃-swap)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; °CCZX ; °CCXZ ; PP-CZ↑)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

private
  X₀² : (₄₊ n) ⊢ X ↓ • X ↓ ≈ ε
  X₀² = X²

-- X on wire 0, as a conjugation.
module N₀ {n : ℕ} = Conj {₄₊ n} (X ↓) X₀²

N₀ᵇ : Bool → Circuit (₄₊ n) → Circuit (₄₊ n)
N₀ᵇ true  w = w
N₀ᵇ false w = N₀.⟪ w ⟫

-- (−1)ᵇ XZ on wire 1, from the wires 0, 3 and, negatively, 2.
rot₁ : Bool → Circuit (₄₊ n)
rot₁ b = S₀₁.⟪ N₂.⟪ rot b ⟫ ⟫

-- The two gates of (240).
A₂₄₀ D₂₄₀ : Bool → Bool → Bool → Circuit (₄₊ n)
A₂₄₀ α β a = N₃ᵇ α (N₁ᵇ β (rot a))
D₂₄₀ γ δ b = N₃ᵇ γ (N₀ᵇ δ (rot₁ b))

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    P q c′ °G′ : Circuit (₄₊ n)
    P   = ΛH₀₁
    q   = CZ ↓
    c′  = P₁₃ CZ
    °G′ = S₀₁.⟪ °ΛH₂′ ⟫

    module Aj = Conj {₄₊ n} PP₀₁ PP₀₁²

    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    --------------------------------------------------------------------
    -- The second gate black on wire 3

    -- (212) under (1 3).
    T₁₃-ZX₃ : T₁₃.⟪ ZX₃ ⟫ ≈ ZX₃
    T₁₃-ZX₃ = T₁₃-via S₂₃-ZX₃ S₁₂-ZX₃ S₂₃-ZX₃

    ZX₃-form₅ : ZX₃ ≈ P • q • P • q
    ZX₃-form₅ = trans (sym T₁₃-ZX₃) (trans (T₁₃.⟪⟫-cong eq212)
      (T₁₃.⟪⟫-•₄ T₁₃-ΛH₂′ T-c T₁₃-ΛH₂′ T-c))
      where
      T-c : T₁₃.⟪ CZ₃₀ ⟫ ≈ q
      T-c = trans (T₁₃.⟪⟫-cong CZ₃₀-P) (T₁₃-P₀₃ CZ)

    -- The CH from wire 3 onto wire 1 passes the box on wire 1: (163)
    -- under (1 3) and the lower swap.
    e163′ : P₁₃ CH • box₃′ ≈ box₃′ • P₁₃ CH
    e163′ = S₀₁.⟪⟫-≈
      (T₁₃.⟪⟫-≈ eq163 (T₁₃.⟪⟫-•₂ (T₁₃-L CH) T₁₃-box₃) (T₁₃.⟪⟫-•₂ T₁₃-box₃ (T₁₃-L CH)))
      (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (P₁₃ CH)) refl) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (P₁₃ CH)))

    -- Between P ⊗ P on the wires 0 1 it is the CZ of the wires 1 3.
    PP-d′ : Aj.⟪ c′ ⟫ ≈ P₁₃ CH
    PP-d′ = S₂₃.⟪⟫-≈ PP-CZ↑ (S₂₃.⟪⟫-•₃ (L-S₂₃ PP) (U-S₂₃ CZ) (L-S₂₃ PP)) (U-S₂₃ CH)

    P-c′ : P • c′ ≈ c′ • P
    P-c′ = sym (Aj.⟪⟫-≈ e163′ (Aj.⟪⟫-•₂ m₁ m₂) (Aj.⟪⟫-•₂ m₂ m₁))
      where
      m₁ : Aj.⟪ P₁₃ CH ⟫ ≈ c′
      m₁ = trans (Aj.⟪⟫-cong (sym PP-d′)) (Aj.⟪⟫-⟪⟫ c′)
      m₂ : Aj.⟪ box₃′ ⟫ ≈ P
      m₂ = sym ΛH₀₁-PP

    P-K : P • K ≈ K • P
    P-K = begin
      P • K                         ≈⟨ back _ K-as-GcGc ⟩
      P • (°G′ • c′ • °G′ • c′)     ≈⟨ comm-abab eq204 P-c′ ⟩
      (°G′ • c′ • °G′ • c′) • P     ≈⟨ front _ (sym K-as-GcGc) ⟩
      K • P ∎

    P-K′ : P • K′ ≈ K′ • P
    P-K′ = begin
      P • K′                        ≈⟨ back _ K′-as-cGcG ⟩
      P • (c′ • °G′ • c′ • °G′)     ≈⟨ comm-abab P-c′ eq204 ⟩
      (c′ • °G′ • c′ • °G′) • P     ≈⟨ front _ (sym K′-as-cGcG) ⟩
      K′ • P ∎

    Z-K : ZX₃ • K ≈ K • ZX₃
    Z-K = begin
      ZX₃ • K                 ≈⟨ front _ ZX₃-form₅ ⟩
      (P • q • P • q) • K     ≈⟨ pass-pqpq P-K P-K′ CZ↓-K CZ↓-K′ ⟩
      K • (P • q • P • q)     ≈⟨ back _ (sym ZX₃-form₅) ⟩
      K • ZX₃ ∎

    Z-K′ : ZX₃ • K′ ≈ K′ • ZX₃
    Z-K′ = comm-inv K-K′ eq209 Z-K

    --------------------------------------------------------------------
    -- The second gate white on wire 3

    N₂-Ex : N₂.⟪ Ex ↓ ⟫ ≈ Ex ↓
    N₂-Ex = N₂.⟪⟫-fix (sym (L-comm Ex X))

    -- (216), mirrored: the first gate passes the doubly controlled ZX on
    -- wire 1, white on wire 2.
    Z-S°W : ZX₃ • S₀₁.⟪ °CCZX ⟫ ≈ S₀₁.⟪ °CCZX ⟫ • ZX₃
    Z-S°W = S₀₁.⟪⟫-≈ (N₂.⟪⟫-≈ eq216 (N₂.⟪⟫-•₂ m refl) (N₂.⟪⟫-•₂ refl m))
      (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ ZX₃) refl) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ ZX₃))
      where
      m : N₂.⟪ K ⟫ ≈ S₀₁.⟪ ZX₃ ⟫
      m = trans (N₂.⟪⟫-•₃ N₂-Ex refl N₂-Ex) (S₀₁.⟪⟫-cong (N₂.⟪⟫-⟪⟫ ZX₃))

    N₃K-form : N₃.⟪ K ⟫ ≈ S₀₁.⟪ °CCZX ⟫ • K′
    N₃K-form = begin
      N₃.⟪ K ⟫                    ≈⟨ sym right-unit ⟩
      N₃.⟪ K ⟫ • ε                ≈⟨ back _ (sym K-K′) ⟩
      N₃.⟪ K ⟫ • K • K′           ≈⟨ sym assoc ⟩
      (N₃.⟪ K ⟫ • K) • K′         ≈⟨ front _ merge₃ ⟩
      S₀₁.⟪ °CCZX ⟫ • K′ ∎
      where
      merge₃ : N₃.⟪ K ⟫ • K ≈ S₀₁.⟪ °CCZX ⟫
      merge₃ = trans (front _ (sym (S₀₁-N₃ (N₂.⟪ ZX₃ ⟫))))
             (trans (sym (S₀₁.⟪⟫-• (N₃.⟪ N₂.⟪ ZX₃ ⟫ ⟫) (N₂.⟪ ZX₃ ⟫))) (S₀₁.⟪⟫-cong °merge-on-3))

    Z-N₃K : ZX₃ • N₃.⟪ K ⟫ ≈ N₃.⟪ K ⟫ • ZX₃
    Z-N₃K = begin
      ZX₃ • N₃.⟪ K ⟫                ≈⟨ back _ N₃K-form ⟩
      ZX₃ • (S₀₁.⟪ °CCZX ⟫ • K′)    ≈⟨ comm-• Z-S°W Z-K′ ⟩
      (S₀₁.⟪ °CCZX ⟫ • K′) • ZX₃    ≈⟨ front _ (sym N₃K-form) ⟩
      N₃.⟪ K ⟫ • ZX₃ ∎

    --------------------------------------------------------------------
    -- Stage 0: everything else black

    rot₁-inv : rot₁ true • rot₁ false ≈ ε
    rot₁-inv = K-K′

    rot₁-inv′ : rot₁ false • rot₁ true ≈ ε
    rot₁-inv′ = eq209

    N₃ᵇ-inv : ∀ γ {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₃ᵇ γ u • N₃ᵇ γ v ≈ ε
    N₃ᵇ-inv true  e = e
    N₃ᵇ-inv false {u} {v} e = trans (sym (N₃.⟪⟫-• u v)) (trans (N₃.⟪⟫-cong e) N₃.⟪⟫-ε)

    core-ZX : ∀ γ → ZX₃ • N₃ᵇ γ (rot₁ true) ≈ N₃ᵇ γ (rot₁ true) • ZX₃
    core-ZX true  = Z-K
    core-ZX false = Z-N₃K

    all-rot : ∀ {g : Circuit (₄₊ n)} → ZX₃ • g ≈ g • ZX₃ → ∀ a → rot a • g ≈ g • rot a
    all-rot e true  = e
    all-rot e false = inv-row eq208′ eq208 e

    stage₀ : ∀ γ a b → rot a • N₃ᵇ γ (rot₁ b) ≈ N₃ᵇ γ (rot₁ b) • rot a
    stage₀ γ a true  = all-rot (core-ZX γ) a
    stage₀ γ a false = all-rot (comm-inv (N₃ᵇ-inv γ rot₁-inv) (N₃ᵇ-inv γ rot₁-inv′) (core-ZX γ)) a

    --------------------------------------------------------------------
    -- X on the wires 0, 1, 3

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    X₀-X₁ : X ↓ • X ↑ ≈ X ↑ • X ↓
    X₀-X₁ = comm-↓↑ X X

    X₀-X₂ : X ↓ • X ↑ ↑ ≈ X ↑ ↑ • X ↓
    X₀-X₂ = comm-↓↑ X (X ↑)

    X₀-X₃ : X ↓ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↓
    X₀-X₃ = comm-↓↑ X (X ↑ ↑)

    -- X on the target turns the rotation over, (238).
    N₀-rot : ∀ a → N₀.⟪ rot (not a) ⟫ ≈ rot a
    N₀-rot false = trans (sym assoc) (trans (front _ eq238) (cancelʳ _ X₀²))
    N₀-rot true  = trans (N₀.⟪⟫-cong (sym (N₀-rot false))) (N₀.⟪⟫-⟪⟫ ZX₃)

    -- The lower swap exchanges X on the wires 0 and 1.
    N₁-S₀₁ : (w : Circuit (₄₊ n)) → N₁.⟪ S₀₁.⟪ w ⟫ ⟫ ≈ S₀₁.⟪ N₀.⟪ w ⟫ ⟫
    N₁-S₀₁ w = sym (S₀₁.⟪⟫-•₃ S-X↓ refl S-X↓)

    N₁-rot₁ : ∀ b → N₁.⟪ rot₁ (not b) ⟫ ≈ rot₁ b
    N₁-rot₁ b = trans (N₁-S₀₁ (N₂.⟪ rot (not b) ⟫))
      (S₀₁.⟪⟫-cong (trans (conj-swap X₀-X₂ (rot (not b))) (N₂.⟪⟫-cong (N₀-rot b))))

    N₁-D : ∀ γ δ b → N₁.⟪ D₂₄₀ γ δ (not b) ⟫ ≈ D₂₄₀ γ δ b
    N₁-D true  true  b = N₁-rot₁ b
    N₁-D true  false b = trans (sym (conj-swap X₀-X₁ (rot₁ (not b)))) (N₀.⟪⟫-cong (N₁-rot₁ b))
    N₁-D false true  b = trans (N₁-N₃-swap (rot₁ (not b))) (N₃.⟪⟫-cong (N₁-rot₁ b))
    N₁-D false false b = trans (N₁-N₃-swap (N₀.⟪ rot₁ (not b) ⟫))
      (N₃.⟪⟫-cong (trans (sym (conj-swap X₀-X₁ (rot₁ (not b)))) (N₀.⟪⟫-cong (N₁-rot₁ b))))

    N₀-N₃ᵇ : ∀ γ (w : Circuit (₄₊ n)) → N₀.⟪ N₃ᵇ γ w ⟫ ≈ N₃ᵇ γ (N₀.⟪ w ⟫)
    N₀-N₃ᵇ true  w = refl
    N₀-N₃ᵇ false w = conj-swap X₀-X₃ w

    flip₃ : ∀ γ (w : Circuit (₄₊ n)) → N₃.⟪ N₃ᵇ (not γ) w ⟫ ≈ N₃ᵇ γ w
    flip₃ true  w = N₃.⟪⟫-⟪⟫ w
    flip₃ false w = refl

    --------------------------------------------------------------------
    -- The stages

    -- The second gate's control on wire 0, the first gate's target.
    stage₁ : ∀ γ δ a b → rot a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • rot a
    stage₁ γ true  a b = stage₀ γ a b
    stage₁ γ false a b = N₀.⟪⟫-≈ (stage₀ γ (not a) b)
      (N₀.⟪⟫-•₂ (N₀-rot a) (N₀-N₃ᵇ γ (rot₁ b)))
      (N₀.⟪⟫-•₂ (N₀-N₃ᵇ γ (rot₁ b)) (N₀-rot a))

    -- The first gate's control on wire 1, the second gate's target.
    stage₂ : ∀ β γ δ a b → N₁ᵇ β (rot a) • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • N₁ᵇ β (rot a)
    stage₂ true  γ δ a b = stage₁ γ δ a b
    stage₂ false γ δ a b = N₁.⟪⟫-≈ (stage₁ γ δ a (not b))
      (N₁.⟪⟫-•₂ refl (N₁-D γ δ b)) (N₁.⟪⟫-•₂ (N₁-D γ δ b) refl)

  -- The second gate's inverse.
  D₂₄₀-inv : ∀ γ δ → D₂₄₀ γ δ true • D₂₄₀ γ δ false ≈ ε
  D₂₄₀-inv γ true  = N₃ᵇ-inv γ rot₁-inv
  D₂₄₀-inv γ false = N₃ᵇ-inv γ (trans (sym (N₀.⟪⟫-• (rot₁ true) (rot₁ false)))
                                       (trans (N₀.⟪⟫-cong rot₁-inv) N₀.⟪⟫-ε))

  D₂₄₀-inv′ : ∀ γ δ → D₂₄₀ γ δ false • D₂₄₀ γ δ true ≈ ε
  D₂₄₀-inv′ γ true  = N₃ᵇ-inv γ rot₁-inv′
  D₂₄₀-inv′ γ false = N₃ᵇ-inv γ (trans (sym (N₀.⟪⟫-• (rot₁ false) (rot₁ true)))
                                        (trans (N₀.⟪⟫-cong rot₁-inv′) N₀.⟪⟫-ε))

  -- (240)
  eq240 : ∀ α β γ δ a b → A₂₄₀ α β a • D₂₄₀ γ δ b ≈ D₂₄₀ γ δ b • A₂₄₀ α β a
  eq240 true  β γ δ a b = stage₂ β γ δ a b
  eq240 false β γ δ a b = N₃.⟪⟫-≈ (stage₂ β (not γ) δ a b)
    (N₃.⟪⟫-•₂ refl (flip₃ γ (N₀ᵇ δ (rot₁ b))))
    (N₃.⟪⟫-•₂ (flip₃ γ (N₀ᵇ δ (rot₁ b))) refl)
