------------------------------------------------------------------------
-- Presentations of groups
--
-- A black gate on the wires 0–3 against a gate on the wires 0 1 2 4 that
-- is white on wire 2 (Clément, Lemma D.7, Equations (253)–(260))
--
-- The first gate is a doubly controlled H: H(1, 3; 0, 2) in (253), (254),
-- (257), (258) and H(0, 1; 2, 3) in the others.  The second, white on
-- wire 2 and with wire 4 where a four-wire gate has wire 3, is
--
--   (253)  Box(1; 0, °2, 4)      (254), (256)  Box(0; 1, °2, 4)
--   (255)  Box(1; 0, °2, 4)      (257), (259)  H(1, 4; 0, °2)
--                                (258), (260)  H(0, 4; 1, °2)
--
-- Each is an equation of Lemma D.5 once both gates sit on the same four
-- wires, and a gate gets there by moving its box wire, `Shift`:
--
--   the first gate has its box wire on wire 3: it passes the swap of the
--     wires 3 4, under which the second gate is a four-wire gate — (192),
--     (182), (201), (203);
--   the second gate has its box wire on wire 4: it is the four-wire gate
--     itself — (204), (202);
--   (255), both box wires on wire 1: under the cycle that carries wire 1
--     to wire 4 the first gate has its box wire there and returns to
--     wire 3; the second has it on wire 4 with wire 3 a control, and
--     returns by way of wire 3 — the braid relation — to the box on
--     wire 2.  The equation is then (186).
--
-- (256) is not of this kind: the two gates need all five wires.  It is
-- at the end of the file.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Colours
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; comm-↓↑ ; CH²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq167)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; eq177)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; ΛH₂′-rot′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (eq182 ; eq186 ; N₂-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (far ; braid↑ ; ΛH₀₁ ; S₁₂-ΛH₂′ ; S₁₂-X₂ ; S₂₃-X₁
        ; module T₁₃ ; T₁₃-ΛH₂′ ; T₁₃-P₁₃ ; T₁₃-P₂₃ ; T₁₃-P₀₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq192 ; °CZ₂₀-ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (box₃‴ ; eq201 ; eq202)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq203 ; eq204)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
  using (module S₃₄ ; Ex₃₄-box₃‴ ; Ex₃₄-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; eq117 ; eq118 ; °CCZX ; °CCXZ ; °CZ₂₀-O)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The first gates

-- H(1, 3; 0, 2) and H(0, 1; 2, 3), on the wires 0–3 of five.
A₁ A₀ : Circuit (₁₊ (₄₊ n))
A₁ = S₀₁.⟪ ΛH₂′ ⟫
A₀ = ΛH₀₁

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  private
    W = Circuit (₁₊ (₄₊ n))

    Ex₃₄ : W
    Ex₃₄ = Ex ↑ ↑ ↑

    --------------------------------------------------------------------
    -- What leaves the wires 3 4 alone carries `passes the swap` along

    S₀₁-Ex₃₄ : S₀₁.⟪ Ex₃₄ ⟫ ≈ Ex₃₄
    S₀₁-Ex₃₄ = P₂₃-S₀₁ (Ex ↑)

    N₂-Ex₃₄ : N₂.⟪ Ex₃₄ ⟫ ≈ Ex₃₄
    N₂-Ex₃₄ = N₂.⟪⟫-fix (lemma-cong↑ (X ↑ • Ex ↑ ↑) (Ex ↑ ↑ • X ↑)
                         (lemma-cong↑ (X ↓ • Ex ↑) (Ex ↑ • X ↓) (comm-↓↑ X Ex)))

    N₁-Ex₃₄ : N₁.⟪ Ex₃₄ ⟫ ≈ Ex₃₄
    N₁-Ex₃₄ = N₁.⟪⟫-fix (lemma-cong↑ (X ↓ • Ex ↑ ↑) (Ex ↑ ↑ • X ↓) (comm-↓↑ X (Ex ↑)))

    via-S₀₁ : ∀ {w : W} → Ex₃₄ • w ≈ w • Ex₃₄ → Ex₃₄ • S₀₁.⟪ w ⟫ ≈ S₀₁.⟪ w ⟫ • Ex₃₄
    via-S₀₁ e = S₀₁.⟪⟫-≈ e (S₀₁.⟪⟫-•₂ S₀₁-Ex₃₄ refl) (S₀₁.⟪⟫-•₂ refl S₀₁-Ex₃₄)

    via-N₂ : ∀ {w : W} → Ex₃₄ • w ≈ w • Ex₃₄ → Ex₃₄ • N₂.⟪ w ⟫ ≈ N₂.⟪ w ⟫ • Ex₃₄
    via-N₂ e = N₂.⟪⟫-≈ e (N₂.⟪⟫-•₂ N₂-Ex₃₄ refl) (N₂.⟪⟫-•₂ refl N₂-Ex₃₄)

    via-N₁ : ∀ {w : W} → Ex₃₄ • w ≈ w • Ex₃₄ → Ex₃₄ • N₁.⟪ w ⟫ ≈ N₁.⟪ w ⟫ • Ex₃₄
    via-N₁ e = N₁.⟪⟫-≈ e (N₁.⟪⟫-•₂ N₁-Ex₃₄ refl) (N₁.⟪⟫-•₂ refl N₁-Ex₃₄)

    Ex₃₄-A₁ : Ex₃₄ • A₁ ≈ A₁ • Ex₃₄
    Ex₃₄-A₁ = via-S₀₁ Ex₃₄-ΛH₂′

    Ex₃₄-°ΛH₂′ : Ex₃₄ • °ΛH₂′ ≈ °ΛH₂′ • Ex₃₄
    Ex₃₄-°ΛH₂′ = via-N₂ Ex₃₄-ΛH₂′

    -- The first gate passes the swap …
    move : ∀ {x y : W} → Ex₃₄ • x ≈ x • Ex₃₄ → x • y ≈ y • x →
           x • S₃₄.⟪ y ⟫ ≈ S₃₄.⟪ y ⟫ • x
    move ex xy = S₃₄.⟪⟫-≈ xy (S₃₄.⟪⟫-•₂ (S₃₄.⟪⟫-fix ex) refl)
                             (S₃₄.⟪⟫-•₂ refl (S₃₄.⟪⟫-fix ex))

    -- … or the second one does.
    move′ : ∀ {x y : W} → Ex₃₄ • y ≈ y • Ex₃₄ → x • y ≈ y • x →
            x • S₃₄.⟪ y ⟫ ≈ S₃₄.⟪ y ⟫ • x
    move′ ey xy = trans (back _ (S₃₄.⟪⟫-fix ey)) (trans xy (front _ (sym (S₃₄.⟪⟫-fix ey))))

  ----------------------------------------------------------------------
  -- (253), (254), (257), (258): the first gate has its box wire on wire 3

  eq253 : A₁ • S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ • A₁
  eq253 = move Ex₃₄-A₁ eq192

  eq254 : A₁ • S₃₄.⟪ °box₃ ⟫ ≈ S₃₄.⟪ °box₃ ⟫ • A₁
  eq254 = move Ex₃₄-A₁ eq182

  eq257 : A₁ • S₃₄.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ≈ S₃₄.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ • A₁
  eq257 = move Ex₃₄-A₁ eq201

  eq258 : A₁ • S₃₄.⟪ °ΛH₂′ ⟫ ≈ S₃₄.⟪ °ΛH₂′ ⟫ • A₁
  eq258 = move Ex₃₄-A₁ eq203

  ----------------------------------------------------------------------
  -- (259), (260): the second gate has its box wire on wire 4

  eq259 : A₀ • S₃₄.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ≈ S₃₄.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ • A₀
  eq259 = move′ (via-S₀₁ Ex₃₄-°ΛH₂′) eq204

  eq260 : A₀ • S₃₄.⟪ °ΛH₂′ ⟫ ≈ S₃₄.⟪ °ΛH₂′ ⟫ • A₀
  eq260 = move′ Ex₃₄-°ΛH₂′ eq202

  ----------------------------------------------------------------------
  -- (255): both box wires on wire 1

  private
    Y₁ Y₂ Y₃ : W
    Y₁ = S₀₁.⟪ °box₃ ⟫
    Y₂ = S₁₂.⟪ Y₁ ⟫
    Y₃ = S₂₃.⟪ Y₂ ⟫

    -- The cycle that carries wire 1 to wire 4.
    ψ : W → W
    ψ w = S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ w ⟫ ⟫ ⟫

    ψ-•₂ : ∀ {a b a′ b′ : W} → ψ a ≈ a′ → ψ b ≈ b′ → ψ (a • b) ≈ a′ • b′
    ψ-•₂ {a} {b} ea eb =
      trans (S₃₄.⟪⟫-cong (trans (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-• a b)) (S₂₃.⟪⟫-• _ _)))
            (S₃₄.⟪⟫-•₂ ea eb)

    ψ-inj : ∀ {x y : W} → ψ x ≈ ψ y → x ≈ y
    ψ-inj {x} {y} e = inj₁₂ (inj₂₃ (inj₃₄ e))
      where
      inj₃₄ : ∀ {x y : W} → S₃₄.⟪ x ⟫ ≈ S₃₄.⟪ y ⟫ → x ≈ y
      inj₃₄ {x} {y} e = trans (sym (S₃₄.⟪⟫-⟪⟫ x)) (trans (S₃₄.⟪⟫-cong e) (S₃₄.⟪⟫-⟪⟫ y))
      inj₂₃ : ∀ {x y : W} → S₂₃.⟪ x ⟫ ≈ S₂₃.⟪ y ⟫ → x ≈ y
      inj₂₃ {x} {y} e = trans (sym (S₂₃.⟪⟫-⟪⟫ x)) (trans (S₂₃.⟪⟫-cong e) (S₂₃.⟪⟫-⟪⟫ y))
      inj₁₂ : ∀ {x y : W} → S₁₂.⟪ x ⟫ ≈ S₁₂.⟪ y ⟫ → x ≈ y
      inj₁₂ {x} {y} e = trans (sym (S₁₂.⟪⟫-⟪⟫ x)) (trans (S₁₂.⟪⟫-cong e) (S₁₂.⟪⟫-⟪⟫ y))

    conj-swap : ∀ {x y : W} → x • y ≈ y • x → (w : W) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    -- The braid relation of the swaps of the wires 2 3 and 3 4.
    braid₃₄ : Ex ↑ ↑ • Ex₃₄ • Ex ↑ ↑ ≈ Ex₃₄ • Ex ↑ ↑ • Ex₃₄
    braid₃₄ = lemma-cong↑ (Ex ↑ • Ex ↑ ↑ • Ex ↑) (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) braid↑

    braid-conj₃₄ : (w : W) → S₃₄.⟪ S₂₃.⟪ S₃₄.⟪ w ⟫ ⟫ ⟫ ≈ S₂₃.⟪ S₃₄.⟪ S₂₃.⟪ w ⟫ ⟫ ⟫
    braid-conj₃₄ w = begin
      Ex₃₄ • (Ex ↑ ↑ • (Ex₃₄ • w • Ex₃₄) • Ex ↑ ↑) • Ex₃₄
        ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
      (Ex₃₄ • Ex ↑ ↑ • Ex₃₄) • w • (Ex₃₄ • Ex ↑ ↑ • Ex₃₄)
        ≈⟨ cong (sym braid₃₄) (back _ (sym braid₃₄)) ⟩
      (Ex ↑ ↑ • Ex₃₄ • Ex ↑ ↑) • w • (Ex ↑ ↑ • Ex₃₄ • Ex ↑ ↑)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      Ex ↑ ↑ • (Ex₃₄ • (Ex ↑ ↑ • w • Ex ↑ ↑) • Ex₃₄) • Ex ↑ ↑ ∎

    -- Under the three lower swaps the box negated on wire 2 is the box on
    -- wire 3 negated on wire 1, which passes the swap of the wires 3 4.
    Y₃-form : Y₃ ≈ N₁.⟪ box₃‴ ⟫
    Y₃-form = begin
      S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ N₂.⟪ box₃ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) refl (P₂₃-S₀₁ X))) ⟩
      S₂₃.⟪ S₁₂.⟪ N₂.⟪ box₃′ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₁₂.⟪⟫-•₃ S₁₂-X₂ refl S₁₂-X₂) ⟩
      S₂₃.⟪ N₁.⟪ S₁₂.⟪ box₃′ ⟫ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-•₃ S₂₃-X₁ refl S₂₃-X₁ ⟩
      N₁.⟪ box₃‴ ⟫ ∎

    Ex₃₄-Y₃ : Ex₃₄ • Y₃ ≈ Y₃ • Ex₃₄
    Ex₃₄-Y₃ = trans (back _ Y₃-form) (trans (via-N₁ Ex₃₄-box₃‴) (front _ (sym Y₃-form)))

    ψ-A₀ : ψ A₀ ≈ ΛH₂′
    ψ-A₀ = S₃₄.⟪⟫-fix Ex₃₄-ΛH₂′

    ψ-B : ψ (S₃₄.⟪ Y₁ ⟫) ≈ Y₂
    ψ-B = begin
      S₃₄.⟪ S₂₃.⟪ S₁₂.⟪ S₃₄.⟪ Y₁ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (S₂₃.⟪⟫-cong (conj-swap far₁₃ Y₁)) ⟩
      S₃₄.⟪ S₂₃.⟪ S₃₄.⟪ Y₂ ⟫ ⟫ ⟫
        ≈⟨ braid-conj₃₄ Y₂ ⟩
      S₂₃.⟪ S₃₄.⟪ Y₃ ⟫ ⟫
        ≈⟨ S₂₃.⟪⟫-cong (S₃₄.⟪⟫-fix Ex₃₄-Y₃) ⟩
      S₂₃.⟪ Y₃ ⟫
        ≈⟨ S₂₃.⟪⟫-⟪⟫ Y₂ ⟩
      Y₂ ∎
      where
      far₁₃ : Ex ↑ • Ex₃₄ ≈ Ex₃₄ • Ex ↑
      far₁₃ = lemma-cong↑ (Ex ↓ • Ex ↑ ↑) (Ex ↑ ↑ • Ex ↓) far

    -- (186), its H gate fixed by the middle swap.
    e186 : ΛH₂′ • Y₂ ≈ Y₂ • ΛH₂′
    e186 = trans (front _ (sym S₁₂-ΛH₂′)) (trans eq186 (back _ S₁₂-ΛH₂′))

  eq255 : A₀ • S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ≈ S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ • A₀
  eq255 = ψ-inj (trans (ψ-•₂ ψ-A₀ ψ-B) (trans e186 (sym (ψ-•₂ ψ-B ψ-A₀))))

  -- The cycle that carries wire 1 to wire 4, for (261): under it the box
  -- on wire 1 from the wires 0 °2 4 is the box on wire 2 from the wires
  -- 0 °1 3.
  cycle₁₄ : Circuit (₁₊ (₄₊ n)) → Circuit (₁₊ (₄₊ n))
  cycle₁₄ = ψ

  cycle₁₄-•₂ : ∀ {a b a′ b′ : Circuit (₁₊ (₄₊ n))} →
               cycle₁₄ a ≈ a′ → cycle₁₄ b ≈ b′ → cycle₁₄ (a • b) ≈ a′ • b′
  cycle₁₄-•₂ = ψ-•₂

  cycle₁₄-inj : ∀ {x y : Circuit (₁₊ (₄₊ n))} → cycle₁₄ x ≈ cycle₁₄ y → x ≈ y
  cycle₁₄-inj = ψ-inj

  cycle₁₄-°box : cycle₁₄ (S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫) ≈ S₁₂.⟪ S₀₁.⟪ °box₃ ⟫ ⟫
  cycle₁₄-°box = ψ-B

------------------------------------------------------------------------
-- (256): the H gate on the box wire of the box
--
-- Neither gate can give up a wire: the two need all five.  But the box
-- is °W B′ °V B′, (177) negated on wire 2, with B′ the box of (255) and
-- °W the doubly controlled ZX on the wires 0 1 2, white on wire 2 — and
-- the H gate passes °W letter by letter: the white CZ from wire 2, and
-- the CH of the wires 0 1 because the H gate is a rotation V a W a
-- around that CH and an involution.

private
  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  -- An involution of the form V a W a passes a.
  rot-comm : ∀ {a W V : Word X} → a • a ≈ ε → W • V ≈ ε → V • W ≈ ε →
             (V • a • W • a) • (V • a • W • a) ≈ ε →
             a • (V • a • W • a) ≈ (V • a • W • a) • a
  rot-comm {a} {W} {V} aa WV VW rr = begin
    a • (V • a • W • a)       ≈⟨ back _ r-inv ⟩
    a • (a • V • a • W)       ≈⟨ cancelˡ _ aa ⟩
    V • a • W                 ≈⟨ sym (cancelʳ _ aa) ⟩
    ((V • a • W) • a) • a     ≈⟨ front _ (by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl) ⟩
    (V • a • W • a) • a ∎
    where
    r r′ : Word X
    r  = V • a • W • a
    r′ = a • V • a • W

    rr′ : r • r′ ≈ ε
    rr′ = begin
      (V • a • W • a) • (a • V • a • W)
        ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
      V • a • W • (a • a) • V • a • W
        ≈⟨ back _ (back _ (back _ (cancelˢ _ aa))) ⟩
      V • a • W • V • a • W
        ≈⟨ back _ (back _ (cancelˡ′ WV)) ⟩
      V • a • a • W
        ≈⟨ back _ (cancelˡ _ aa) ⟩
      V • W
        ≈⟨ VW ⟩
      ε ∎
      where
      cancelˡ′ : ∀ {u v s : Word X} → u • v ≈ ε → u • v • s ≈ s
      cancelˡ′ e = trans (sym assoc) (trans (front _ e) left-unit)

    r-inv : r ≈ r′
    r-inv = begin
      r                 ≈⟨ sym right-unit ⟩
      r • ε             ≈⟨ back _ (sym rr′) ⟩
      r • r • r′        ≈⟨ sym assoc ⟩
      (r • r) • r′      ≈⟨ front _ rr ⟩
      ε • r′            ≈⟨ left-unit ⟩
      r′ ∎

private
  -- The H gate on the wires 0 1 as a rotation of wire 1 around the CH
  -- below: (1 3) on the form of the H gate with its box wire on wire 3.
  ΛH₀₁-rot : (₄₊ n) ⊢ ΛH₀₁ ≈ CCXZ ↑ • CH ↓ • CCZX ↑ • CH ↓
  ΛH₀₁-rot {n} = trans (sym T₁₃-ΛH₂′) (trans (T₁₃.⟪⟫-cong ΛH₂′-rot′)
    (T₁₃.⟪⟫-•₄ (T₁₃.⟪⟫-•₄ T-d T-h T-d T-h) (T₁₃-P₀₃ CH)
               (T₁₃.⟪⟫-•₄ T-h T-d T-h T-d) (T₁₃-P₀₃ CH)))
    where
    open Tools ((₄₊ n) VRel,_===_)
    T-d : T₁₃.⟪ P₁₃ CZ ⟫ ≈ P₁₃ CZ
    T-d = trans (T₁₃-P₁₃ CZ)
                (S₁₂.⟪⟫-cong (lemma-cong↑ (U (Ex • CZ • Ex)) (U CZ) (U-sem (Ex • CZ • Ex) CZ Eq.refl)))
    T-h : T₁₃.⟪ P₂₃ HC ⟫ ≈ U CH
    T-h = trans (T₁₃-P₂₃ HC) (U-sem (Ex • HC • Ex) CH Eq.refl)

  ΛH₀₁² : (₄₊ n) ⊢ ΛH₀₁ • ΛH₀₁ ≈ ε
  ΛH₀₁² = S₀₁.⟪⟫-invol eq167

  a-ΛH₀₁ : (₄₊ n) ⊢ CH ↓ • ΛH₀₁ ≈ ΛH₀₁ • CH ↓
  a-ΛH₀₁ {n} = trans (back _ ΛH₀₁-rot) (trans (rot-comm Γ CH² WV VW rr) (front _ (sym ΛH₀₁-rot)))
    where
    Γ = (₄₊ n) VRel,_===_
    open Tools Γ
    WV : CCZX ↑ • CCXZ ↑ ≈ ε
    WV = lemma-cong↑ (CCZX • CCXZ) ε eq117
    VW : CCXZ ↑ • CCZX ↑ ≈ ε
    VW = lemma-cong↑ (CCXZ • CCZX) ε eq118
    rr : (CCXZ ↑ • CH ↓ • CCZX ↑ • CH ↓) • (CCXZ ↑ • CH ↓ • CCZX ↑ • CH ↓) ≈ ε
    rr = trans (sym (cong ΛH₀₁-rot ΛH₀₁-rot)) ΛH₀₁²

  °b-ΛH₀₁ : (₄₊ n) ⊢ °CZ₂₀ • ΛH₀₁ ≈ ΛH₀₁ • °CZ₂₀
  °b-ΛH₀₁ {n} = trans (front _ °CZ₂₀-O) (trans °CZ₂₀-ΛH₀₁ (back _ (sym °CZ₂₀-O)))
    where open Tools ((₄₊ n) VRel,_===_)

  N₂-a : (₄₊ n) ⊢ N₂.⟪ CH ↓ ⟫ ≈ CH ↓
  N₂-a {n} = N₂.⟪⟫-fix (sym (L-comm CH X))
    where open Tools ((₄₊ n) VRel,_===_)

  ΛH₀₁-°W : (₄₊ n) ⊢ ΛH₀₁ • °CCZX ≈ °CCZX • ΛH₀₁
  ΛH₀₁-°W {n} = trans (back _ form) (trans (comm-abab (sym a-ΛH₀₁) (sym °b-ΛH₀₁)) (front _ (sym form)))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    form : °CCZX ≈ CH ↓ • °CZ₂₀ • CH ↓ • °CZ₂₀
    form = N₂.⟪⟫-•₄ N₂-a refl N₂-a refl

  ΛH₀₁-°V : (₄₊ n) ⊢ ΛH₀₁ • °CCXZ ≈ °CCXZ • ΛH₀₁
  ΛH₀₁-°V {n} = trans (back _ form) (trans (comm-abab (sym °b-ΛH₀₁) (sym a-ΛH₀₁)) (front _ (sym form)))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    form : °CCXZ ≈ °CZ₂₀ • CH ↓ • °CZ₂₀ • CH ↓
    form = N₂.⟪⟫-•₄ refl N₂-a refl N₂-a

  -- (177), negated on wire 2.
  °box-177 : (₄₊ n) ⊢ °box₃ ≈ °CCZX • S₀₁.⟪ °box₃ ⟫ • °CCXZ • S₀₁.⟪ °box₃ ⟫
  °box-177 {n} = trans (N₂.⟪⟫-cong eq177) (N₂.⟪⟫-•₄ refl N₂-box₃′ refl N₂-box₃′)
    where open Tools ((₄₊ n) VRel,_===_)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    B′ : Circuit (₁₊ (₄₊ n))
    B′ = S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫

    B-form : S₃₄.⟪ °box₃ ⟫ ≈ °CCZX • B′ • °CCXZ • B′
    B-form = trans (S₃₄.⟪⟫-cong °box-177)
                   (S₃₄.⟪⟫-•₄ (S₃₄.⟪⟫-fix (sym (L₃-top °CCZX Ex))) refl
                              (S₃₄.⟪⟫-fix (sym (L₃-top °CCXZ Ex))) refl)

  eq256 : A₀ • S₃₄.⟪ °box₃ ⟫ ≈ S₃₄.⟪ °box₃ ⟫ • A₀
  eq256 = begin
    A₀ • S₃₄.⟪ °box₃ ⟫
      ≈⟨ back _ B-form ⟩
    A₀ • (°CCZX • B′ • °CCXZ • B′)
      ≈⟨ comm-• ΛH₀₁-°W (comm-• eq255 (comm-• ΛH₀₁-°V eq255)) ⟩
    (°CCZX • B′ • °CCXZ • B′) • A₀
      ≈⟨ front _ (sym B-form) ⟩
    S₃₄.⟪ °box₃ ⟫ • A₀ ∎
