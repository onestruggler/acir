------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P against a crossed one of
-- the other colour with a control on wire 4 (Clément, Lemma D.7,
-- Equation (267))
--
-- The first gate is that of (242), the rotation of wire 0 between P ⊗ P
-- on the wires 0 1, with controls of any colour on the wires 1 and 3.
-- The second rotates wire 1 from wire 4, from wire 2 negatively, and
-- from wire 0 in either colour: the second gate of (242) with wire 4 in
-- the place of wire 3.
--
-- All black, the first gate is G′ P G′ P and the second °G′₄ °B₄ °G′₄ °B₄
-- — the first and second gates of (253)–(260) — and the letters pass
-- each other: (257), (254), (259), (256).  Every colour is then a
-- symmetry of the family, as in the paper:
--
--   wire 3: X there, which the second gate does not see;
--   wire 1: Z H Z there — between P ⊗ P it is X on the control of the
--     first gate, and on the target of the second gate it exchanges ZX
--     and XZ, (236) and (237);
--   wire 0: X there — between P ⊗ P it is Z H Z on the target of the
--     first gate, and it changes the colour of the second gate's control.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies267
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; comm-↓↑ ; H² ; Z² ; X² ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃
  using (eq236 ; eq237)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; A₂₄₁ ; N₁-N₃-swap)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃
  using (module N₀ ; N₀ᵇ ; rot₁ ; D₂₄₀ ; D₂₄₀-inv ; D₂₄₀-inv′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (module Aj ; Aᴾ ; Aᴾ-form ; Aᴾ-inv ; Aᴾ-inv′ ; N₃-Aᴾ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃
  using (°ZX₃-as-GBGB)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
  using (module S₃₄ ; conj-swap ; L₄-top)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Colours complete₂ complete₃
  using (eq254 ; eq256 ; eq257 ; eq259)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The second gate

-- The rotation of wire 1 from wire 4, from wire 2 negatively, and from
-- wire 0 in either colour.
G₂₆₇ : Bool → Bool → Circuit (₁₊ (₄₊ n))
G₂₆₇ γ b = S₃₄.⟪ D₂₄₀ true γ b ⟫

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    W₅ = Circuit (₁₊ (₄₊ n))

    Ex₃₄ X₄ zhz₀ zhz₁ °G′₄ °B₄ : W₅
    Ex₃₄ = Ex ↑ ↑ ↑
    X₄   = X ↑ ↑ ↑ ↑
    zhz₀ = Z ↓ • H ↓ • Z ↓
    zhz₁ = Z ↑ • H ↑ • Z ↑
    °G′₄ = S₃₄.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫
    °B₄  = S₃₄.⟪ °box₃ ⟫

    inv-row : ∀ {w v y : W₅} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    words : ∀ {x₁ x₂ y₁ y₂ : W₅} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (x₁ • x₂ • x₁ • x₂) • (y₁ • y₂ • y₁ • y₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
    words e₁₁ e₁₂ e₂₁ e₂₂ =
      sym (comm-abab (sym (comm-abab e₁₁ e₁₂)) (sym (comm-abab e₂₁ e₂₂)))

    --------------------------------------------------------------------
    -- All black

    G-form : G₂₆₇ true true ≈ °G′₄ • °B₄ • °G′₄ • °B₄
    G-form = trans (S₃₄.⟪⟫-cong (trans (S₀₁.⟪⟫-cong °ZX₃-as-GBGB)
                     (S₀₁.⟪⟫-•₄ refl (S₀₁.⟪⟫-⟪⟫ °box₃) refl (S₀₁.⟪⟫-⟪⟫ °box₃))))
                   (S₃₄.⟪⟫-•₄ refl refl refl refl)

    base : Aᴾ true true true • G₂₆₇ true true ≈ G₂₆₇ true true • Aᴾ true true true
    base = begin
      Aᴾ true true true • G₂₆₇ true true
        ≈⟨ cong Aᴾ-form G-form ⟩
      (S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁ • S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁) • (°G′₄ • °B₄ • °G′₄ • °B₄)
        ≈⟨ words eq257 eq254 eq259 eq256 ⟩
      (°G′₄ • °B₄ • °G′₄ • °B₄) • (S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁ • S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁)
        ≈⟨ sym (cong G-form Aᴾ-form) ⟩
      G₂₆₇ true true • Aᴾ true true true ∎

    --------------------------------------------------------------------
    -- Signs

    G-inv : ∀ γ → G₂₆₇ γ true • G₂₆₇ γ false ≈ ε
    G-inv γ = trans (sym (S₃₄.⟪⟫-• _ _)) (trans (S₃₄.⟪⟫-cong (D₂₄₀-inv true γ)) S₃₄.⟪⟫-ε)

    G-inv′ : ∀ γ → G₂₆₇ γ false • G₂₆₇ γ true ≈ ε
    G-inv′ γ = trans (sym (S₃₄.⟪⟫-• _ _)) (trans (S₃₄.⟪⟫-cong (D₂₄₀-inv′ true γ)) S₃₄.⟪⟫-ε)

    signs₁ : ∀ b → Aᴾ true true true • G₂₆₇ true b ≈ G₂₆₇ true b • Aᴾ true true true
    signs₁ true  = base
    signs₁ false = comm-inv (G-inv true) (G-inv′ true) base

    signs : ∀ a b → Aᴾ true true a • G₂₆₇ true b ≈ G₂₆₇ true b • Aᴾ true true a
    signs true  b = signs₁ b
    signs false b = inv-row (Aᴾ-inv true true) (Aᴾ-inv′ true true) (signs₁ b)

    --------------------------------------------------------------------
    -- Z H Z on wire 0 exchanges ZX and XZ there

    zhz₀² : zhz₀ • zhz₀ ≈ ε
    zhz₀² = L-sem ((Z ↓ • H ↓ • Z ↓) • (Z ↓ • H ↓ • Z ↓)) ε Eq.refl

    zhz₁² : zhz₁ • zhz₁ ≈ ε
    zhz₁² = L-sem ((Z ↑ • H ↑ • Z ↑) • (Z ↑ • H ↑ • Z ↑)) ε Eq.refl

    module Zh = Conj {₁₊ (₄₊ n)} zhz₀ zhz₀²
    module R  = Conj {₁₊ (₄₊ n)} zhz₁ zhz₁²

    flip-pass : ∀ {x w w′ : W₅} → x • x ≈ ε → x • w ≈ w′ • x → x • w′ ≈ w • x
    flip-pass xx e = sym (conj-comm xx (trans (sym assoc) (trans (front _ e) (cancelʳ _ xx))))

    pass₃ : ∀ {x y w w′ : W₅} → x • w ≈ w′ • x → y • w′ ≈ w • y →
            (x • y • x) • w ≈ w′ • (x • y • x)
    pass₃ {x} {y} {w} {w′} xw yw′ = begin
      (x • y • x) • w       ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      x • y • (x • w)       ≈⟨ back _ (back _ xw) ⟩
      x • y • (w′ • x)      ≈⟨ by-passoc (□ • □ • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      x • (y • w′) • x      ≈⟨ back _ (front _ yw′) ⟩
      x • (w • y) • x       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (x • w) • y • x       ≈⟨ front _ xw ⟩
      (w′ • x) • y • x      ≈⟨ assoc ⟩
      w′ • (x • y • x) ∎

    unpass : ∀ {w w′ : W₅} → zhz₀ • w ≈ w′ • zhz₀ → Zh.⟪ w ⟫ ≈ w′
    unpass e = trans (sym assoc) (trans (front _ e) (cancelʳ _ zhz₀²))

    Zh-rot : ∀ a → Zh.⟪ rot (not a) ⟫ ≈ rot a
    Zh-rot true  = unpass (pass₃ eq237 eq236)
    Zh-rot false = unpass (pass₃ (flip-pass Z² eq237) (flip-pass H² eq236))

    --------------------------------------------------------------------
    -- Commuting one-wire gates

    zhz₀-X₁ : zhz₀ • X ↑ ≈ X ↑ • zhz₀
    zhz₀-X₁ = comm-↓↑ (Z • H • Z) X

    zhz₀-X₂ : zhz₀ • X ↑ ↑ ≈ X ↑ ↑ • zhz₀
    zhz₀-X₂ = L-comm (Z ↓ • H ↓ • Z ↓) X

    zhz₀-X₃ : zhz₀ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • zhz₀
    zhz₀-X₃ = L-comm (Z ↓ • H ↓ • Z ↓) (X ↑)

    X₀-zhz₁ : X ↓ • zhz₁ ≈ zhz₁ • X ↓
    X₀-zhz₁ = comm-↓↑ X (Z • H • Z)

    X₀-Ex₃₄ : X ↓ • Ex₃₄ ≈ Ex₃₄ • X ↓
    X₀-Ex₃₄ = comm-↓↑ X (Ex ↑ ↑)

    zhz₁-Ex₃₄ : zhz₁ • Ex₃₄ ≈ Ex₃₄ • zhz₁
    zhz₁-Ex₃₄ = lemma-cong↑ ((Z ↓ • H ↓ • Z ↓) • Ex ↑ ↑) (Ex ↑ ↑ • (Z ↓ • H ↓ • Z ↓))
                  (comm-↓↑ (Z • H • Z) (Ex ↑))

    --------------------------------------------------------------------
    -- Wire 0: X

    -- Between P ⊗ P, X on wire 0 is Z H Z.
    Aj-zhz₀ : Aj.⟪ zhz₀ ⟫ ≈ X ↓
    Aj-zhz₀ = L-sem (PP • (Z ↓ • H ↓ • Z ↓) • PP) (X ↓) Eq.refl

    N₀-Aj : (w : W₅) → N₀.⟪ Aj.⟪ w ⟫ ⟫ ≈ Aj.⟪ Zh.⟪ w ⟫ ⟫
    N₀-Aj w = begin
      X ↓ • Aj.⟪ w ⟫ • X ↓
        ≈⟨ cong (sym Aj-zhz₀) (back _ (sym Aj-zhz₀)) ⟩
      Aj.⟪ zhz₀ ⟫ • Aj.⟪ w ⟫ • Aj.⟪ zhz₀ ⟫
        ≈⟨ sym (Aj.⟪⟫-•₃ refl refl refl) ⟩
      Aj.⟪ zhz₀ • w • zhz₀ ⟫ ∎

    Zh-N₁ᵇ : ∀ β a → Zh.⟪ N₁ᵇ β (rot (not a)) ⟫ ≈ N₁ᵇ β (rot a)
    Zh-N₁ᵇ true  a = Zh-rot a
    Zh-N₁ᵇ false a = trans (conj-swap zhz₀-X₁ (rot (not a))) (N₁.⟪⟫-cong (Zh-rot a))

    Zh-A : ∀ α β a → Zh.⟪ A₂₄₁ α β (not a) ⟫ ≈ A₂₄₁ α β a
    Zh-A true  β a = Zh-N₁ᵇ β a
    Zh-A false β a = trans (conj-swap zhz₀-X₃ (N₁ᵇ β (rot (not a)))) (N₃.⟪⟫-cong (Zh-N₁ᵇ β a))

    N₀-Aᴾ : ∀ α β a → N₀.⟪ Aᴾ α β (not a) ⟫ ≈ Aᴾ α β a
    N₀-Aᴾ α β a = trans (N₀-Aj (A₂₄₁ α β (not a))) (Aj.⟪⟫-cong (Zh-A α β a))

    N₀-G : ∀ γ b → N₀.⟪ G₂₆₇ (not γ) b ⟫ ≈ G₂₆₇ γ b
    N₀-G true  b = trans (conj-swap X₀-Ex₃₄ (N₀.⟪ rot₁ b ⟫)) (S₃₄.⟪⟫-cong (N₀.⟪⟫-⟪⟫ (rot₁ b)))
    N₀-G false b = conj-swap X₀-Ex₃₄ (rot₁ b)

    stage-γ : ∀ γ a b → Aᴾ true true a • G₂₆₇ γ b ≈ G₂₆₇ γ b • Aᴾ true true a
    stage-γ true  a b = signs a b
    stage-γ false a b = N₀.⟪⟫-≈ (signs (not a) b)
      (N₀.⟪⟫-•₂ (N₀-Aᴾ true true a) (N₀-G false b))
      (N₀.⟪⟫-•₂ (N₀-G false b) (N₀-Aᴾ true true a))

    --------------------------------------------------------------------
    -- Wire 1: Z H Z

    -- Between P ⊗ P, Z H Z on wire 1 is X there.
    Aj-X₁ : Aj.⟪ X ↑ ⟫ ≈ zhz₁
    Aj-X₁ = L-sem (PP • X ↑ • PP) (Z ↑ • H ↑ • Z ↑) Eq.refl

    R-Aj : (w : W₅) → R.⟪ Aj.⟪ w ⟫ ⟫ ≈ Aj.⟪ N₁.⟪ w ⟫ ⟫
    R-Aj w = begin
      zhz₁ • Aj.⟪ w ⟫ • zhz₁
        ≈⟨ cong (sym Aj-X₁) (back _ (sym Aj-X₁)) ⟩
      Aj.⟪ X ↑ ⟫ • Aj.⟪ w ⟫ • Aj.⟪ X ↑ ⟫
        ≈⟨ sym (Aj.⟪⟫-•₃ refl refl refl) ⟩
      Aj.⟪ N₁.⟪ w ⟫ ⟫ ∎

    N₁-A : ∀ α β a → N₁.⟪ A₂₄₁ α (not β) a ⟫ ≈ A₂₄₁ α β a
    N₁-A true  true  a = N₁.⟪⟫-⟪⟫ (rot a)
    N₁-A true  false a = refl
    N₁-A false true  a = trans (N₁-N₃-swap (N₁.⟪ rot a ⟫)) (N₃.⟪⟫-cong (N₁.⟪⟫-⟪⟫ (rot a)))
    N₁-A false false a = N₁-N₃-swap (rot a)

    R-Aᴾ : ∀ α β a → R.⟪ Aᴾ α (not β) a ⟫ ≈ Aᴾ α β a
    R-Aᴾ α β a = trans (R-Aj (A₂₄₁ α (not β) a)) (Aj.⟪⟫-cong (N₁-A α β a))

    S₀₁-zhz : S₀₁.⟪ zhz₀ ⟫ ≈ zhz₁
    S₀₁-zhz = L-sem (Ex • (Z ↓ • H ↓ • Z ↓) • Ex) (Z ↑ • H ↑ • Z ↑) Eq.refl

    R-rot₁ : ∀ b → R.⟪ rot₁ (not b) ⟫ ≈ rot₁ b
    R-rot₁ b = begin
      zhz₁ • S₀₁.⟪ N₂.⟪ rot (not b) ⟫ ⟫ • zhz₁
        ≈⟨ sym (S₀₁.⟪⟫-•₃ S₀₁-zhz refl S₀₁-zhz) ⟩
      S₀₁.⟪ Zh.⟪ N₂.⟪ rot (not b) ⟫ ⟫ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (trans (conj-swap zhz₀-X₂ (rot (not b))) (N₂.⟪⟫-cong (Zh-rot b))) ⟩
      S₀₁.⟪ N₂.⟪ rot b ⟫ ⟫ ∎

    R-D : ∀ γ b → R.⟪ D₂₄₀ true γ (not b) ⟫ ≈ D₂₄₀ true γ b
    R-D true  b = R-rot₁ b
    R-D false b = trans (conj-swap (sym X₀-zhz₁) (rot₁ (not b))) (N₀.⟪⟫-cong (R-rot₁ b))

    R-G : ∀ γ b → R.⟪ G₂₆₇ γ (not b) ⟫ ≈ G₂₆₇ γ b
    R-G γ b = trans (conj-swap zhz₁-Ex₃₄ (D₂₄₀ true γ (not b))) (S₃₄.⟪⟫-cong (R-D γ b))

    stage-β : ∀ β γ a b → Aᴾ true β a • G₂₆₇ γ b ≈ G₂₆₇ γ b • Aᴾ true β a
    stage-β true  γ a b = stage-γ γ a b
    stage-β false γ a b = R.⟪⟫-≈ (stage-γ γ a (not b))
      (R.⟪⟫-•₂ (R-Aᴾ true false a) (R-G γ b))
      (R.⟪⟫-•₂ (R-G γ b) (R-Aᴾ true false a))

    --------------------------------------------------------------------
    -- Wire 3: X, which the second gate does not see

    X₄² : X₄ • X₄ ≈ ε
    X₄² = lemma-cong↑ (X ↑ ↑ ↑ • X ↑ ↑ ↑) ε (lemma-cong↑ (X ↑ ↑ • X ↑ ↑) ε
            (lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)))

    module N₄ = Conj {₁₊ (₄₊ n)} X₄ X₄²

    S₃₄-X₄ : S₃₄.⟪ X₄ ⟫ ≈ X ↑ ↑ ↑
    S₃₄-X₄ = lemma-cong↑ (Ex ↑ ↑ • X ↑ ↑ ↑ • Ex ↑ ↑) (X ↑ ↑)
               (lemma-cong↑ (Ex ↑ • X ↑ ↑ • Ex ↑) (X ↑)
                 (lemma-cong↑ (Ex • X ↑ • Ex) (X ↓) S-X↑))

    N₄-rot : ∀ b → N₄.⟪ rot b ⟫ ≈ rot b
    N₄-rot true  = N₄.⟪⟫-fix (sym (L₄-top (ΛZX 3) X))
    N₄-rot false = N₄.⟪⟫-fix (sym (L₄-top (ΛXZ 3) X))

    X₄-X₂ : X₄ • X ↑ ↑ ≈ X ↑ ↑ • X₄
    X₄-X₂ = sym (lemma-cong↑ (X ↑ • X ↑ ↑ ↑) (X ↑ ↑ ↑ • X ↑)
                  (lemma-cong↑ (X ↓ • X ↑ ↑) (X ↑ ↑ • X ↓) (comm-↓↑ X (X ↑))))

    X₄-X₀ : X₄ • X ↓ ≈ X ↓ • X₄
    X₄-X₀ = sym (comm-↓↑ X (X ↑ ↑ ↑))

    X₄-Ex : X₄ • Ex ↓ ≈ Ex ↓ • X₄
    X₄-Ex = sym (L-comm Ex (X ↑ ↑))

    N₄-rot₁ : ∀ b → N₄.⟪ rot₁ b ⟫ ≈ rot₁ b
    N₄-rot₁ b = trans (conj-swap X₄-Ex (N₂.⟪ rot b ⟫))
               (S₀₁.⟪⟫-cong (trans (conj-swap X₄-X₂ (rot b)) (N₂.⟪⟫-cong (N₄-rot b))))

    N₄-D : ∀ γ b → N₄.⟪ D₂₄₀ true γ b ⟫ ≈ D₂₄₀ true γ b
    N₄-D true  b = N₄-rot₁ b
    N₄-D false b = trans (conj-swap X₄-X₀ (rot₁ b)) (N₀.⟪⟫-cong (N₄-rot₁ b))

    N₃-G : ∀ γ b → N₃.⟪ G₂₆₇ γ b ⟫ ≈ G₂₆₇ γ b
    N₃-G γ b = begin
      X ↑ ↑ ↑ • S₃₄.⟪ D₂₄₀ true γ b ⟫ • X ↑ ↑ ↑
        ≈⟨ cong (sym S₃₄-X₄) (back _ (sym S₃₄-X₄)) ⟩
      S₃₄.⟪ X₄ ⟫ • S₃₄.⟪ D₂₄₀ true γ b ⟫ • S₃₄.⟪ X₄ ⟫
        ≈⟨ sym (S₃₄.⟪⟫-•₃ refl refl refl) ⟩
      S₃₄.⟪ N₄.⟪ D₂₄₀ true γ b ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (N₄-D γ b) ⟩
      S₃₄.⟪ D₂₄₀ true γ b ⟫ ∎

  -- (267)
  eq267 : ∀ α β γ a b → Aᴾ α β a • G₂₆₇ γ b ≈ G₂₆₇ γ b • Aᴾ α β a
  eq267 true  β γ a b = stage-β β γ a b
  eq267 false β γ a b = N₃.⟪⟫-≈ (stage-β β γ a b)
    (N₃.⟪⟫-•₂ (N₃-Aᴾ β a) (N₃-G γ b)) (N₃.⟪⟫-•₂ (N₃-G γ b) (N₃-Aᴾ β a))
