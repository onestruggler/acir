------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P against a white CZ (Clément,
-- Lemma D.5, Equations (247), (248))
--
-- The second gate is the CZ of the wires 1 2, white on wire 2 and of
-- either colour on wire 1.  The first is, between P ⊗ P on the wires 0 1,
-- the rotation of wire 0 from the wires 1, 2, 3, (248), or its image
-- under the lower swap, the rotation of wire 1, (247); its controls on
-- the wires 1 (or 0) and 3 have any colours.
--
-- Between P ⊗ P the CZ becomes a CH onto wire 1, white on wire 2, (112),
-- and the statement one about the rotation itself: that CH passes the
-- rotation letter by letter in the form (212) — the H gate between its
-- own P ⊗ P by (164) — and the doubly controlled rotation a white control
-- on wire 1 adds, (230).  For (247) the CH is onto wire 0: (232), (233),
-- and one three-wire evaluation.  The second white control is −Z on
-- wire 2, (229).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies247
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals247 complete₂ complete₃
  using (ev-°CH-CCZX)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (eq164)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (CCZX₂₃ ; CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₃ ; box₃‴ ; ΛH₂′-PP ; N₂-PP₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (T₀₃-via ; T₀₃-box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃
  using (eq229 ; eq229′ ; eq230 ; eq232 ; eq233 ; °CH₂₀-as-O)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; A₂₄₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; °CH₂₀ ; °CZ₂₀-O ; PP-CZ↑ ; PP-CZ₂₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The CZ of the wires 1 2, white on wire 2, black or white on wire 1.
E₂₄₇ : Bool → Circuit (₄₊ n)
E₂₄₇ true  = U °CZ
E₂₄₇ false = U °CZ°

-- The first gate of (247): the rotation of wire 1 between P ⊗ P.
Fᴾ : Bool → Bool → Bool → Circuit (₄₊ n)
Fᴾ α β a = Aj.⟪ S₀₁.⟪ A₂₄₁ α β a ⟫ ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    t t₀ z° c G : Circuit (₄₊ n)
    t  = U °CH
    t₀ = °CH₂₀
    z° = Z° ↑ ↑
    c  = CZ₃₀
    G  = ΛH₂′

    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    N₁ZX₃-form : N₁.⟪ ZX₃ ⟫ ≈ CCZX₂₃ • XZ₃
    N₁ZX₃-form = begin
      N₁.⟪ ZX₃ ⟫                    ≈⟨ sym right-unit ⟩
      N₁.⟪ ZX₃ ⟫ • ε                ≈⟨ back _ (sym eq208′) ⟩
      N₁.⟪ ZX₃ ⟫ • ZX₃ • XZ₃        ≈⟨ sym assoc ⟩
      (N₁.⟪ ZX₃ ⟫ • ZX₃) • XZ₃      ≈⟨ front _ merge₁ ⟩
      CCZX₂₃ • XZ₃ ∎

    N₁-inv : N₁.⟪ ZX₃ ⟫ • N₁.⟪ XZ₃ ⟫ ≈ ε
    N₁-inv = trans (sym (N₁.⟪⟫-• ZX₃ XZ₃)) (trans (N₁.⟪⟫-cong eq208′) N₁.⟪⟫-ε)

    N₁-inv′ : N₁.⟪ XZ₃ ⟫ • N₁.⟪ ZX₃ ⟫ ≈ ε
    N₁-inv′ = trans (sym (N₁.⟪⟫-• XZ₃ ZX₃)) (trans (N₁.⟪⟫-cong eq208) N₁.⟪⟫-ε)

    -- A gate that passes the black ZX, the doubly controlled ZX from the
    -- wires 2 3 and X on wire 3 passes the rotation in all its colours.
    all-A : ∀ {g : Circuit (₄₊ n)} → g • ZX₃ ≈ ZX₃ • g → g • CCZX₂₃ ≈ CCZX₂₃ • g →
            g • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • g → ∀ α β a → g • A₂₄₁ α β a ≈ A₂₄₁ α β a • g
    all-A {g} gZ gW gX = stage-α
      where
      gZ′ : g • XZ₃ ≈ XZ₃ • g
      gZ′ = comm-inv eq208′ eq208 gZ
      gN : g • N₁.⟪ ZX₃ ⟫ ≈ N₁.⟪ ZX₃ ⟫ • g
      gN = trans (back _ N₁ZX₃-form) (trans (comm-• gW gZ′) (front _ (sym N₁ZX₃-form)))
      stage-β : ∀ β a → g • N₁ᵇ β (rot a) ≈ N₁ᵇ β (rot a) • g
      stage-β true  true  = gZ
      stage-β true  false = gZ′
      stage-β false true  = gN
      stage-β false false = comm-inv N₁-inv N₁-inv′ gN
      stage-α : ∀ α β a → g • A₂₄₁ α β a ≈ A₂₄₁ α β a • g
      stage-α true  β a = stage-β β a
      stage-α false β a = comm-• gX (comm-• (stage-β β a) gX)

    --------------------------------------------------------------------
    -- The CH onto wire 1, white on wire 2

    T₀₃-U : (u : Circuit 2) → T₀₃.⟪ U u ⟫ ≈ U u
    T₀₃-U u = T₀₃-via {w₁ = O u} refl (T₁₃-O u) (S₀₁.⟪⟫-⟪⟫ (U u))

    t-c : t • c ≈ c • t
    t-c = begin
      t • c             ≈⟨ back _ CZ₃₀-P ⟩
      t • P₀₃ CZ        ≈⟨ sym (P₀₃-U CZ °CH) ⟩
      P₀₃ CZ • t        ≈⟨ front _ (sym CZ₃₀-P) ⟩
      c • t ∎

    t-PP : t • PP₀₃ ≈ PP₀₃ • t
    t-PP = sym (P₀₃-U PP °CH)

    -- (164) under (0 3): the box on wire 3.
    t-β₃ : t • box₃‴ ≈ box₃‴ • t
    t-β₃ = T₀₃.⟪⟫-≈ eq164 (T₀₃.⟪⟫-•₂ (T₀₃-U °CH) T₀₃-box₃) (T₀₃.⟪⟫-•₂ T₀₃-box₃ (T₀₃-U °CH))

    t-G : t • G ≈ G • t
    t-G = begin
      t • G                           ≈⟨ back _ ΛH₂′-PP ⟩
      t • (PP₀₃ • box₃‴ • PP₀₃)       ≈⟨ comm-• t-PP (comm-• t-β₃ t-PP) ⟩
      (PP₀₃ • box₃‴ • PP₀₃) • t       ≈⟨ front _ (sym ΛH₂′-PP) ⟩
      G • t ∎

    t-ZX₃ : t • ZX₃ ≈ ZX₃ • t
    t-ZX₃ = trans (back _ eq212) (trans (comm-abab t-G t-c) (front _ (sym eq212)))

    t-X₃ : t • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • t
    t-X₃ = L₃-top (U₀ °CH) X

    t-A : ∀ α β a → t • A₂₄₁ α β a ≈ A₂₄₁ α β a • t
    t-A = all-A t-ZX₃ eq230 t-X₃

    --------------------------------------------------------------------
    -- −Z on wire 2

    z°-W₂₃ : z° • CCZX₂₃ ≈ CCZX₂₃ • z°
    z°-W₂₃ = trans (back _ (sym merge₁)) (trans (comm-• z°-N eq229) (front _ merge₁))
      where
      X₁-z° : X ↑ • z° ≈ z° • X ↑
      X₁-z° = lemma-cong↑ (X ↓ • Z° ↑) (Z° ↑ • X ↓) (comm-↓↑ X Z°)
      z°-N : z° • N₁.⟪ ZX₃ ⟫ ≈ N₁.⟪ ZX₃ ⟫ • z°
      z°-N = comm-• (sym X₁-z°) (comm-• eq229 (sym X₁-z°))

    z°-X₃ : z° • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • z°
    z°-X₃ = L₃-top (Z° ↑ ↑) X

    z°-A : ∀ α β a → z° • A₂₄₁ α β a ≈ A₂₄₁ α β a • z°
    z°-A = all-A eq229 z°-W₂₃ z°-X₃

    --------------------------------------------------------------------
    -- P ⊗ P on the wires 0 1 and the second gate

    X₂-PP : X ↑ ↑ • PP₀₁ ≈ PP₀₁ • X ↑ ↑
    X₂-PP = N₂.⟪⟫-comm N₂-PP₀₁

    -- (112), white on wire 2.
    Aj-E₁ : Aj.⟪ E₂₄₇ true ⟫ ≈ t
    Aj-E₁ = trans (conj-swap (sym X₂-PP) (CZ ↑)) (N₂.⟪⟫-cong PP-CZ↑)

    Aj-z° : Aj.⟪ z° ⟫ ≈ z°
    Aj-z° = Aj.⟪⟫-fix (L-comm PP Z°)

    E₀-form : E₂₄₇ false ≈ z° • E₂₄₇ true
    E₀-form = U-sem °CZ° (Z° ↑ • °CZ) Eq.refl

    back-A : ∀ {w w′ : Circuit (₄₊ n)} → Aj.⟪ w ⟫ ≈ w′ → Aj.⟪ w′ ⟫ ≈ w
    back-A {w} e = trans (Aj.⟪⟫-cong (sym e)) (Aj.⟪⟫-⟪⟫ w)

    E₁-Aᴾ : ∀ α β a → E₂₄₇ true • Aᴾ α β a ≈ Aᴾ α β a • E₂₄₇ true
    E₁-Aᴾ α β a = Aj.⟪⟫-≈ (t-A α β a) (Aj.⟪⟫-•₂ (back-A Aj-E₁) refl) (Aj.⟪⟫-•₂ refl (back-A Aj-E₁))

    z°-Aᴾ : ∀ α β a → z° • Aᴾ α β a ≈ Aᴾ α β a • z°
    z°-Aᴾ α β a = Aj.⟪⟫-≈ (z°-A α β a) (Aj.⟪⟫-•₂ Aj-z° refl) (Aj.⟪⟫-•₂ refl Aj-z°)

  -- (248)
  eq248 : ∀ α β γ a → Aᴾ α β a • E₂₄₇ γ ≈ E₂₄₇ γ • Aᴾ α β a
  eq248 α β true  a = sym (E₁-Aᴾ α β a)
  eq248 α β false a = trans (back _ E₀-form)
    (trans (comm-• (sym (z°-Aᴾ α β a)) (sym (E₁-Aᴾ α β a))) (front _ (sym E₀-form)))

  ----------------------------------------------------------------------
  -- (247)

  private
    -- The CH onto wire 0, white on wire 2: (232), and the doubly
    -- controlled ZX by evaluation.
    t₀-W₂₃ : t₀ • CCZX₂₃ ≈ CCZX₂₃ • t₀
    t₀-W₂₃ = trans (front _ °CH₂₀-as-O) (trans (O₃-comm-ev ev-°CH-CCZX) (back _ (sym °CH₂₀-as-O)))

    t₀-X₃ : t₀ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • t₀
    t₀-X₃ = L₃-top °CH₂₀ X

    t₀-A : ∀ α β a → t₀ • A₂₄₁ α β a ≈ A₂₄₁ α β a • t₀
    t₀-A = all-A eq232 t₀-W₂₃ t₀-X₃

    -- The second gate under the lower swap, and between P ⊗ P.
    Aj-°CZ₂₀ : Aj.⟪ °CZ₂₀ ⟫ ≈ t₀
    Aj-°CZ₂₀ = trans (conj-swap (sym X₂-PP) CZ₂₀) (N₂.⟪⟫-cong PP-CZ₂₀)

    °CZ₂₀-Aᴾ : ∀ α β a → °CZ₂₀ • Aᴾ α β a ≈ Aᴾ α β a • °CZ₂₀
    °CZ₂₀-Aᴾ α β a = Aj.⟪⟫-≈ (t₀-A α β a)
      (Aj.⟪⟫-•₂ (back-A Aj-°CZ₂₀) refl) (Aj.⟪⟫-•₂ refl (back-A Aj-°CZ₂₀))

    PP-Ex : PP₀₁ • Ex ↓ ≈ Ex ↓ • PP₀₁
    PP-Ex = L-sem (PP • Ex) (Ex • PP) Eq.refl

    -- The first gate is the image of that of (248) under the lower swap.
    Fᴾ-form : ∀ α β a → S₀₁.⟪ Aᴾ α β a ⟫ ≈ Fᴾ α β a
    Fᴾ-form α β a = conj-swap (sym PP-Ex) (A₂₄₁ α β a)

    S-z° : S₀₁.⟪ z° ⟫ ≈ z°
    S-z° = P₂₃-S₀₁ Z°

    E₁-Fᴾ : ∀ α β a → E₂₄₇ true • Fᴾ α β a ≈ Fᴾ α β a • E₂₄₇ true
    E₁-Fᴾ α β a = S₀₁.⟪⟫-≈ (°CZ₂₀-Aᴾ α β a)
      (S₀₁.⟪⟫-•₂ m (Fᴾ-form α β a)) (S₀₁.⟪⟫-•₂ (Fᴾ-form α β a) m)
      where
      m : S₀₁.⟪ °CZ₂₀ ⟫ ≈ E₂₄₇ true
      m = trans (S₀₁.⟪⟫-cong °CZ₂₀-O) (S₀₁.⟪⟫-⟪⟫ (U °CZ))

    z°-Fᴾ : ∀ α β a → z° • Fᴾ α β a ≈ Fᴾ α β a • z°
    z°-Fᴾ α β a = S₀₁.⟪⟫-≈ (z°-Aᴾ α β a)
      (S₀₁.⟪⟫-•₂ S-z° (Fᴾ-form α β a)) (S₀₁.⟪⟫-•₂ (Fᴾ-form α β a) S-z°)

  eq247 : ∀ α β γ a → Fᴾ α β a • E₂₄₇ γ ≈ E₂₄₇ γ • Fᴾ α β a
  eq247 α β true  a = sym (E₁-Fᴾ α β a)
  eq247 α β false a = trans (back _ E₀-form)
    (trans (comm-• (sym (z°-Fᴾ α β a)) (sym (E₁-Fᴾ α β a))) (front _ (sym E₀-form)))
