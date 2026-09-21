------------------------------------------------------------------------
-- Presentations of groups
--
-- A rotation between P ⊗ P on the pairs 2 3 and 0 1 against a rotation
-- of the other colour on wire 4 (Clément, Lemma D.7, Equations
-- (263)–(266))
--
-- The first gate is a triply controlled rotation on the wires 0 1 2 4 —
-- of wire 1 in (263), (264), of wire 0 in (265), (266) — between P ⊗ P
-- on the wires 2 3 and on the wires 0 1; wire 3 is idle but for P ⊗ P.
-- The second gate is white on wire 4 and rotates wire 2 ((263), (265))
-- or wire 0 ((264), (266)), with a control of either colour on wire 1.
--
-- Under the swap of the wires 3 4 both rotations sit on the wires 0–3
-- and wire 4 is idle but for P ⊗ P, on the pairs 2 4 and 0 1, which by
-- (246) are also the pairs 0 4 and 1 2.  P ⊗ P on the target of a
-- rotation and the idle wire turns it over, (262) — `Pairs` —, so:
--
--   (264)  P ⊗ P on 0 4 turns the second gate over, and what is left is
--          (244);
--   (266)  it turns the first gate over too, and what is left is (245);
--   (263)  P ⊗ P on 2 4 turns the second gate over, and what is left is
--          (244) under the transposition of the wires 0 2;
--   (265)  P ⊗ P on 0 4 turns the first gate over, and what is left is
--          (244) again: negated on wire 3, under the middle swap, and
--          between P ⊗ P on the wires 1 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies263
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
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (braid-conj ; S₁₂-X₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₃ ; PP₁₃ ; PP₁₃² ; PP-triangle ; klein-ca ; S₀₁-N₃ ; S₁₂-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₁₂² ; N₃-PP₁₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; S₁₂-ZX₃ ; S₁₂-XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (PP₂₃ ; PP₂₃² ; PP-triangle₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies245 complete₂ complete₃
  using (module Pj ; N₂ᵇ ; F₂₄₅ ; S₂₄₅ ; eq245)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies244 complete₂ complete₃
  using (F₂₄₄ ; eq244)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
  using (module S₃₄ ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Pairs complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The gates

-- P ⊗ P on the pairs 2 3 and 0 1.
Π₂₆₃ : Circuit (₄₊ n)
Π₂₆₃ = PP₂₃ • PP₀₁

-- The first gates: the rotation of wire 1, resp. wire 0, from the other
-- of the two and the wires 2 4, between the P ⊗ P.
G¹₂₆₃ G⁰₂₆₃ : Bool → Circuit (₁₊ (₄₊ n))
G¹₂₆₃ a = Π₂₆₃ • S₃₄.⟪ S₀₁.⟪ rot a ⟫ ⟫ • Π₂₆₃
G⁰₂₆₃ a = Π₂₆₃ • S₃₄.⟪ rot a ⟫ • Π₂₆₃

-- The second gates, white on wire 4: the rotation of wire 2 from wire 0
-- and, in either colour, wire 1; and that of wire 0 from wire 2 and, in
-- either colour, wire 1.
H²₂₆₃ H⁰₂₆₃ : Bool → Bool → Circuit (₁₊ (₄₊ n))
H²₂₆₃ α b = S₃₄.⟪ J₂₆₃ α b ⟫
H⁰₂₆₃ α b = S₃₄.⟪ S₂₄₅ α b ⟫

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  -- x turns y over and f passes y turned over: x f x passes y.
  conj-inv-comm : ∀ {x f y y′ : Word X} → x • y ≈ y′ • x → x • y′ ≈ y • x →
                  f • y′ ≈ y′ • f → (x • f • x) • y ≈ y • (x • f • x)
  conj-inv-comm {x} {f} {y} {y′} xy xy′ fy′ = begin
    (x • f • x) • y       ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    x • f • (x • y)       ≈⟨ back _ (back _ xy) ⟩
    x • f • (y′ • x)      ≈⟨ by-passoc (□ • □ • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    x • (f • y′) • x      ≈⟨ back _ (front _ fy′) ⟩
    x • (y′ • f) • x      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (x • y′) • f • x      ≈⟨ front _ xy′ ⟩
    (y • x) • f • x       ≈⟨ assoc ⟩
    y • (x • f • x) ∎

------------------------------------------------------------------------
-- Four-wire facts

private
  -- (246), the other way: the pairs 2 3 and 0 1 are the pairs 0 3 and 1 2.
  e246′ : (₄₊ n) ⊢ Π₂₆₃ ≈ PP₀₃ • PP₁₂
  e246′ {n} = sym (begin
    PP₀₃ • PP₁₂
      ≈⟨ front _ (sym PP-triangle) ⟩
    (PP₀₁ • PP₁₃) • PP₁₂
      ≈⟨ front _ (back _ (sym (klein-ca Γ PP₁₂² PP₁₃² PP₂₃² PP-triangle₃))) ⟩
    (PP₀₁ • PP₂₃ • PP₁₂) • PP₁₂
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • (□ • □) • □) Eq.refl ⟩
    PP₀₁ • (PP₂₃ • PP₁₂) • PP₁₂
      ≈⟨ back _ (cancelʳ _ PP₁₂²) ⟩
    PP₀₁ • PP₂₃
      ≈⟨ sym (P₂₃-L PP PP) ⟩
    PP₂₃ • PP₀₁ ∎)
    where
    Γ = (₄₊ n) VRel,_===_
    open Tools Γ

  S₁₂-PP : (₄₊ n) ⊢ S₁₂.⟪ PP₁₂ ⟫ ≈ PP₁₂
  S₁₂-PP = U-sem (Ex • PP • Ex) PP Eq.refl

  S₁₂-rot : ∀ b → (₄₊ n) ⊢ S₁₂.⟪ rot b ⟫ ≈ rot b
  S₁₂-rot true  = S₁₂-ZX₃
  S₁₂-rot false = S₁₂-XZ₃

  -- The middle swap carries the second gate of (244) to the rotation
  -- with its coloured control on wire 2.
  S₁₂-S : ∀ β b → (₄₊ n) ⊢ S₁₂.⟪ S₂₄₅ β b ⟫ ≈ V₂₆₃ β b
  S₁₂-S {n} true  b = trans (S₁₂-N₃ (rot b)) (N₃.⟪⟫-cong (S₁₂-rot b))
    where open Tools ((₄₊ n) VRel,_===_)
  S₁₂-S {n} false b = trans (S₁₂-N₃ (N₁.⟪ rot b ⟫))
    (N₃.⟪⟫-cong (S₁₂.⟪⟫-•₃ S₁₂-X₁ (S₁₂-rot b) S₁₂-X₁))
    where open Tools ((₄₊ n) VRel,_===_)

  -- (244) under the transposition of the wires 0 2.
  e244θ : ∀ β a b → (₄₊ n) ⊢ (PP₀₁ • S₀₁.⟪ rot a ⟫ • PP₀₁) • J₂₆₃ β b
                          ≈ J₂₆₃ β b • (PP₀₁ • S₀₁.⟪ rot a ⟫ • PP₀₁)
  e244θ {n} β a b = trans (sym (cong θ-F θ-S))
                   (trans (sym (θ-• _ _)) (trans (θ-cong (eq244 true β a b))
                   (trans (θ-• _ _) (cong θ-S θ-F))))
    where
    open Tools ((₄₊ n) VRel,_===_)
    θ : Circuit (₄₊ n) → Circuit (₄₊ n)
    θ w = S₁₂.⟪ S₀₁.⟪ S₁₂.⟪ w ⟫ ⟫ ⟫
    θ-cong : ∀ {x y} → x ≈ y → θ x ≈ θ y
    θ-cong e = S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong e))
    θ-• : ∀ x y → θ (x • y) ≈ θ x • θ y
    θ-• x y = trans (S₁₂.⟪⟫-cong (trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-• x y)) (S₀₁.⟪⟫-• _ _)))
                    (S₁₂.⟪⟫-• _ _)
    θ-•₃ : ∀ x y z → θ (x • y • z) ≈ θ x • θ y • θ z
    θ-•₃ x y z = trans (θ-• x (y • z)) (back _ (θ-• y z))
    θ-PP : θ PP₁₂ ≈ PP₀₁
    θ-PP = trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong S₁₂-PP))
                 (trans (S₁₂.⟪⟫-cong (sym (O-L PP))) (S₁₂.⟪⟫-⟪⟫ PP₀₁))
    θ-K : θ (S₀₁.⟪ rot a ⟫) ≈ S₀₁.⟪ rot a ⟫
    θ-K = trans (braid-conj (S₀₁.⟪ rot a ⟫))
         (S₀₁.⟪⟫-cong (trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ (rot a))) (S₁₂-rot a)))
    θ-F : θ (F₂₄₄ true a) ≈ PP₀₁ • S₀₁.⟪ rot a ⟫ • PP₀₁
    θ-F = trans (θ-•₃ PP₁₂ (S₀₁.⟪ rot a ⟫) PP₁₂) (cong θ-PP (cong θ-K θ-PP))
    θ-S : θ (S₂₄₅ β b) ≈ J₂₆₃ β b
    θ-S = S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong (S₁₂-S β b))

  -- (244) negated on wire 3, under the middle swap, between P ⊗ P.
  e244ᴾ : ∀ α a b → (₄₊ n) ⊢ F₂₄₅ true a • J₂₆₃ α b ≈ J₂₆₃ α b • F₂₄₅ true a
  e244ᴾ {n} α a b = sym (Pj.⟪⟫-≈ e₂ (Pj.⟪⟫-•₂ (Pj.⟪⟫-⟪⟫ (J₂₆₃ α b)) refl)
                                   (Pj.⟪⟫-•₂ refl (Pj.⟪⟫-⟪⟫ (J₂₆₃ α b))))
    where
    open Tools ((₄₊ n) VRel,_===_)
    X₃-PP : X ↑ ↑ ↑ • PP₁₂ ≈ PP₁₂ • X ↑ ↑ ↑
    X₃-PP = N₃.⟪⟫-comm N₃-PP₁₂
    conj-swap₄ : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                 x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap₄ {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎
    N₃-F : N₃.⟪ F₂₄₄ α b ⟫ ≈ Pj.⟪ S₀₁.⟪ V₂₆₃ α b ⟫ ⟫
    N₃-F = trans (conj-swap₄ X₃-PP (S₀₁.⟪ N₂ᵇ α (rot b) ⟫))
                 (Pj.⟪⟫-cong (sym (S₀₁-N₃ (N₂ᵇ α (rot b)))))
    e₁ : Pj.⟪ S₀₁.⟪ V₂₆₃ α b ⟫ ⟫ • rot a ≈ rot a • Pj.⟪ S₀₁.⟪ V₂₆₃ α b ⟫ ⟫
    e₁ = N₃.⟪⟫-≈ (eq244 α true b a) (N₃.⟪⟫-•₂ N₃-F (N₃.⟪⟫-⟪⟫ (rot a)))
                                     (N₃.⟪⟫-•₂ (N₃.⟪⟫-⟪⟫ (rot a)) N₃-F)
    S₁₂-Pj : S₁₂.⟪ Pj.⟪ S₀₁.⟪ V₂₆₃ α b ⟫ ⟫ ⟫ ≈ Pj.⟪ J₂₆₃ α b ⟫
    S₁₂-Pj = S₁₂.⟪⟫-•₃ S₁₂-PP refl S₁₂-PP
    e₂ : Pj.⟪ J₂₆₃ α b ⟫ • rot a ≈ rot a • Pj.⟪ J₂₆₃ α b ⟫
    e₂ = S₁₂.⟪⟫-≈ e₁ (S₁₂.⟪⟫-•₂ S₁₂-Pj (S₁₂-rot a)) (S₁₂.⟪⟫-•₂ (S₁₂-rot a) S₁₂-Pj)

------------------------------------------------------------------------
-- (263)–(266)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  private
    W₅ = Circuit (₁₊ (₄₊ n))

    Π₄ : W₅
    Π₄ = PP₂₄ • PP₀₁

    --------------------------------------------------------------------
    -- P ⊗ P under the swap of the wires 3 4

    S₃₄-PP₀₁ : S₃₄.⟪ PP₀₁ ⟫ ≈ PP₀₁
    S₃₄-PP₀₁ = S₃₄.⟪⟫-fix (sym (L-comm PP (Ex ↑)))

    S₃₄-PP₁₂ : S₃₄.⟪ PP₁₂ ⟫ ≈ PP₁₂
    S₃₄-PP₁₂ = S₃₄.⟪⟫-fix (sym (L₃-top (PP ↑) Ex))

    S₃₄-Π₄ : S₃₄.⟪ Π₄ ⟫ ≈ Π₂₆₃
    S₃₄-Π₄ = S₃₄.⟪⟫-•₂ (S₃₄.⟪⟫-⟪⟫ PP₂₃) S₃₄-PP₀₁

    -- The pairs 2 4 and 0 1 are the pairs 0 4 and 1 2, either way round.
    Π₄-form : Π₄ ≈ PP₀₄ • PP₁₂
    Π₄-form = trans (sym (S₃₄.⟪⟫-•₂ refl S₃₄-PP₀₁))
             (trans (S₃₄.⟪⟫-cong e246′) (S₃₄.⟪⟫-•₂ refl S₃₄-PP₁₂))

    PP₀₄-PP₁₂ : PP₀₄ • PP₁₂ ≈ PP₁₂ • PP₀₄
    PP₀₄-PP₁₂ = S₃₄.⟪⟫-≈ (P₀₃-U PP PP) (S₃₄.⟪⟫-•₂ refl S₃₄-PP₁₂) (S₃₄.⟪⟫-•₂ S₃₄-PP₁₂ refl)

    Π₄-form′ : Π₄ ≈ PP₁₂ • PP₀₄
    Π₄-form′ = trans Π₄-form PP₀₄-PP₁₂

    Π₄-swap : Π₄ ≈ PP₀₁ • PP₂₄
    Π₄-swap = S₃₄.⟪⟫-≈ (P₂₃-L PP PP) (S₃₄.⟪⟫-•₂ refl S₃₄-PP₀₁) (S₃₄.⟪⟫-•₂ S₃₄-PP₀₁ refl)

    --------------------------------------------------------------------
    -- The first gates under the swap of the wires 3 4

    -- The rotation of wire 1: P ⊗ P on the wires 0 4 stays outside, and
    -- inside is the first gate of (244) …
    K¹-form : ∀ a → Π₄ • S₀₁.⟪ rot a ⟫ • Π₄ ≈ PP₀₄ • F₂₄₄ true a • PP₀₄
    K¹-form a = begin
      Π₄ • S₀₁.⟪ rot a ⟫ • Π₄
        ≈⟨ cong Π₄-form (back _ Π₄-form′) ⟩
      (PP₀₄ • PP₁₂) • S₀₁.⟪ rot a ⟫ • (PP₁₂ • PP₀₄)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      PP₀₄ • (PP₁₂ • S₀₁.⟪ rot a ⟫ • PP₁₂) • PP₀₄ ∎

    -- … or P ⊗ P on the wires 2 4 stays outside.
    K¹-form′ : ∀ a → Π₄ • S₀₁.⟪ rot a ⟫ • Π₄ ≈ PP₂₄ • (PP₀₁ • S₀₁.⟪ rot a ⟫ • PP₀₁) • PP₂₄
    K¹-form′ a = begin
      Π₄ • S₀₁.⟪ rot a ⟫ • Π₄
        ≈⟨ back _ (back _ Π₄-swap) ⟩
      (PP₂₄ • PP₀₁) • S₀₁.⟪ rot a ⟫ • (PP₀₁ • PP₂₄)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      PP₂₄ • (PP₀₁ • S₀₁.⟪ rot a ⟫ • PP₀₁) • PP₂₄ ∎

    -- The rotation of wire 0: P ⊗ P on the wires 0 4 turns it over, and
    -- it is the first gate of (245).
    K⁰-form : ∀ a → Π₄ • rot a • Π₄ ≈ F₂₄₅ true (not a)
    K⁰-form a = begin
      Π₄ • rot a • Π₄
        ≈⟨ cong Π₄-form′ (back _ Π₄-form) ⟩
      (PP₁₂ • PP₀₄) • rot a • (PP₀₄ • PP₁₂)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • ((□ • □) • □) • □) Eq.refl ⟩
      PP₁₂ • ((PP₀₄ • rot a) • PP₀₄) • PP₁₂
        ≈⟨ back _ (front _ (trans (front _ (PP₀₄-rot a)) (cancelʳ _ PP₀₄²))) ⟩
      PP₁₂ • rot (not a) • PP₁₂ ∎

    --------------------------------------------------------------------
    -- The four equations under the swap

    f264 : ∀ α a b → (Π₄ • S₀₁.⟪ rot a ⟫ • Π₄) • S₂₄₅ α b ≈ S₂₄₅ α b • (Π₄ • S₀₁.⟪ rot a ⟫ • Π₄)
    f264 α a b = trans (front _ (K¹-form a))
      (trans (conj-inv-comm Γ (PP₀₄-S α b) (flip-pass Γ PP₀₄² (PP₀₄-S α b)) (eq244 true α a (not b)))
             (back _ (sym (K¹-form a))))

    f263 : ∀ α a b → (Π₄ • S₀₁.⟪ rot a ⟫ • Π₄) • J₂₆₃ α b ≈ J₂₆₃ α b • (Π₄ • S₀₁.⟪ rot a ⟫ • Π₄)
    f263 α a b = trans (front _ (K¹-form′ a))
      (trans (conj-inv-comm Γ (PP₂₄-J α b) (flip-pass Γ PP₂₄² (PP₂₄-J α b)) (e244θ α a (not b)))
             (back _ (sym (K¹-form′ a))))
      where
      PP₂₄² : PP₂₄ • PP₂₄ ≈ ε
      PP₂₄² = S₃₄.⟪⟫-invol PP₂₃²

    f266 : ∀ α a b → (Π₄ • rot a • Π₄) • S₂₄₅ α b ≈ S₂₄₅ α b • (Π₄ • rot a • Π₄)
    f266 α a b = trans (front _ (K⁰-form a)) (trans (eq245 true α (not a) b) (back _ (sym (K⁰-form a))))

    f265 : ∀ α a b → (Π₄ • rot a • Π₄) • J₂₆₃ α b ≈ J₂₆₃ α b • (Π₄ • rot a • Π₄)
    f265 α a b = trans (front _ (K⁰-form a)) (trans (e244ᴾ α (not a) b) (back _ (sym (K⁰-form a))))

    -- Back under the swap.
    back₃₄ : ∀ {k y : W₅} → (Π₄ • k • Π₄) • y ≈ y • (Π₄ • k • Π₄) →
             (Π₂₆₃ • S₃₄.⟪ k ⟫ • Π₂₆₃) • S₃₄.⟪ y ⟫ ≈ S₃₄.⟪ y ⟫ • (Π₂₆₃ • S₃₄.⟪ k ⟫ • Π₂₆₃)
    back₃₄ e = S₃₄.⟪⟫-≈ e (S₃₄.⟪⟫-•₂ (S₃₄.⟪⟫-•₃ S₃₄-Π₄ refl S₃₄-Π₄) refl)
                          (S₃₄.⟪⟫-•₂ refl (S₃₄.⟪⟫-•₃ S₃₄-Π₄ refl S₃₄-Π₄))

  eq263 : ∀ α a b → G¹₂₆₃ a • H²₂₆₃ α b ≈ H²₂₆₃ α b • G¹₂₆₃ a
  eq263 α a b = back₃₄ (f263 α a b)

  eq264 : ∀ α a b → G¹₂₆₃ a • H⁰₂₆₃ α b ≈ H⁰₂₆₃ α b • G¹₂₆₃ a
  eq264 α a b = back₃₄ (f264 α a b)

  eq265 : ∀ α a b → G⁰₂₆₃ a • H²₂₆₃ α b ≈ H²₂₆₃ α b • G⁰₂₆₃ a
  eq265 α a b = back₃₄ (f265 α a b)

  eq266 : ∀ α a b → G⁰₂₆₃ a • H⁰₂₆₃ α b ≈ H⁰₂₆₃ α b • G⁰₂₆₃ a
  eq266 α a b = back₃₄ (f266 α a b)
