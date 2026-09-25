------------------------------------------------------------------------
-- Presentations of groups
--
-- The triply controlled ZX on the box wire of a box with wire 3 idle
-- (Clément, Lemma D.12, Equation (319))
--
-- At width 5 + k, with the wires numbered from the bottom as D = 0,
-- C = 1, B = 2, A = 3 and the top wires 4 …: the triply controlled ZX
-- on wire 0 from the wires 1 2 3, and its inverse XZ₃, pass the box on
-- wire 0 controlled by the wires 1 2 in any colours and by the top
-- wires, wire 3 idle (`eq319`, `eq319′`).  The paper does the colour of
-- wire 1 as two cases, each a chain of merges.  Here one semantic step
-- one width down, with wire 3 idle, writes such a box as a product of
-- at most four: the box with both controls black (Box₃), without the
-- control on wire 2 (C′), without the one on wire 1 (β₂), and without
-- either (β∅) — the set {w₁ = a, w₂ = b} is a symmetric difference of
-- {w₁ = w₂ = 1}, {w₁ = 1}, {w₂ = 1} and the whole.  ZX₃ passes each:
-- Box₃ by (291) under the swap of the wires 2 3, which fixes ZX₃
-- ((214)); C′ by (290); β₂ by (290) under the swap of the wires 1 2
-- ((215)); and β∅, whose box wire moves to wire 3 along the idle wires
-- ((274)), by (308), the box wire being a dirty ancilla for the wires
-- below it — with one control only (k = 0) it is Z on the top wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Gadget319
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; m<n+m)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₁₂ ; module S₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′ ; eq214 ; eq215)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (N₁ᵇ ; rot)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; box274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; boxAt ; eq308)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoBoxes complete₂ complete₃
  using (eq290 ; eq291 ; B₁₀↑-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; cf-Λ↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀ ; module Forms)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemBoxes using (C₀ ; sem-C₀-yB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
  using (CF ; cf-• ; cf-loc ; cf-loc′ ; cf-↑ ; cf-box ; cf-~)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals using (Ex₁₂ᴸ ; Ex₁₂ᴸ-def)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-low ; place-cong ; place-high ; lemma-5-1 ; ↑ᵏ-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-step ; placeAt-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (place-yB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem)

------------------------------------------------------------------------
-- The box with no control below the top wires passes ZX₃

-- The box on wire 2 controlled by the top wires, the wires 0 1 3 idle.
β∅ : ∀ k → Circuit (₁₊ (₄₊ k))
β∅ k = place 3 (Λ□ (₁₊ k) ↑ ↑)

ZX₃-β∅ : ∀ k → Below (₁₊ (₄₊ k)) → (₁₊ (₄₊ k)) ⊢ ZX₃ • β∅ k ≈ β∅ k • ZX₃
ZX₃-β∅ zero _ = begin
  ZX₃ • β∅ 0          ≈⟨ back _ br ⟩
  ZX₃ • Z ↑ ↑ ↑ ↑     ≈⟨ local-comm (ΛZX 3) Z ⟩
  Z ↑ ↑ ↑ ↑ • ZX₃     ≈⟨ front _ (sym br) ⟩
  β∅ 0 • ZX₃ ∎
  where
  open Tools (5 VRel,_===_)

  -- With one control the box is Z on it.
  box₁ : 2 ⊢ Λ□ 1 ≈ Z ↑
  box₁ = complete₂ (same-sem (Λ□ 1) (Z ↑) Eq.refl)

  hi : 5 ⊢ place 3 (Z ↑ ↑ ↑) ≈ Z ↑ ↑ ↑ ↑
  hi = Eq.subst₂ (λ a b → 5 ⊢ place 3 a ≈ b)
         (Eq.trans (Eq.sym (↑ᵏ-↑ Z 2)) (Eq.cong _↑ (Eq.sym (↑ᵏ-↑ Z 1))))
         (Eq.trans (Eq.sym (↑ᵏ-↑ Z 3)) (Eq.cong _↑ (Eq.trans (Eq.sym (↑ᵏ-↑ Z 2)) (Eq.cong _↑ (Eq.sym (↑ᵏ-↑ Z 1))))))
         (place-high 3 Z)

  br : 5 ⊢ β∅ 0 ≈ Z ↑ ↑ ↑ ↑
  br = trans (place-cong 3 (lemma-cong↑ _ _ (lemma-cong↑ _ _ box₁))) hi
ZX₃-β∅ (suc k) below = begin
  ZX₃ • β∅ (suc k)          ≈⟨ back _ br ⟩
  ZX₃ • boxAt (₂₊ k) 3      ≈⟨ eq308 k 3 below (ΛZX 3) ⟩
  boxAt (₂₊ k) 3 • ZX₃      ≈⟨ front _ (sym br) ⟩
  β∅ (suc k) • ZX₃ ∎
  where
  open Tools ((₁₊ (₄₊ (suc k))) VRel,_===_)

  u : Circuit (₄₊ (suc k))
  u = Λ□ (₂₊ k) ↑ ↑

  complete : Complete k
  complete = below (m<n+m (₃₊ k) {3} (s≤s z≤n))

  -- place 3 is place 2 between the swaps of the wires 2 3.
  step : placeAt 3 u ≈ Ex ↑ ↑ • placeAt 2 u • Ex ↑ ↑
  step = placeAt-step 2 u (s≤s (s≤s (s≤s z≤n)))

  hi : place 2 u ≈ Λ□ (₂₊ k) ↑ ↑ ↑
  hi = Eq.subst₂ (λ a b → place 2 a ≈ b)
         (Eq.sym (↑ᵏ-↑ (Λ□ (₂₊ k)) 1))
         (Eq.trans (Eq.sym (↑ᵏ-↑ (Λ□ (₂₊ k)) 2)) (Eq.cong _↑ (Eq.sym (↑ᵏ-↑ (Λ□ (₂₊ k)) 1))))
         (place-high 2 (Λ□ (₂₊ k)))

  -- The box wire moves from wire 2 to the idle wire 3: (274), two up.
  wire : Ex ↑ ↑ • Λ□ (₂₊ k) ↑ ↑ ↑ • Ex ↑ ↑ ≈ Λ□ (₂₊ k) ↑ ↑ ↑
  wire = lemma-cong↑ _ _ (lemma-cong↑ _ _ (box274 k complete))

  br : β∅ (suc k) ≈ boxAt (₂₊ k) 3
  br = begin
    place 3 u                            ≈⟨ ≡→≈ (Eq.sym (placeAt-place 3 u)) ⟩
    placeAt 3 u                          ≈⟨ step ⟩
    Ex ↑ ↑ • placeAt 2 u • Ex ↑ ↑        ≈⟨ back _ (front _ (trans (≡→≈ (placeAt-place 2 u)) hi)) ⟩
    Ex ↑ ↑ • Λ□ (₂₊ k) ↑ ↑ ↑ • Ex ↑ ↑    ≈⟨ wire ⟩
    Λ□ (₂₊ k) ↑ ↑ ↑ ∎
    where
    ≡→≈ : ∀ {a b} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- (319)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    complete : Complete (₁₊ k)
    complete = below (n<1+n (₄₊ k))

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)

  ----------------------------------------------------------------------
  -- The boxes, wire 3 idle

  -- The box on wire 0 controlled by the wires 1 2 and the top wires.
  Box₃ : Circuit N
  Box₃ = place 3 (Λ□ (₃₊ k))

  -- The same without the control on wire 2, and without the one on
  -- wire 1.
  C′ β₂ : Circuit N
  C′ = place 3 (C₀ k)
  β₂ = place 3 (Ex ↑ • C₀ k • Ex ↑)

  -- A control on wire 2 of either colour (black = true).
  N₂ᵇ : Bool → Circuit N → Circuit N
  N₂ᵇ true  w = w
  N₂ᵇ false w = N₂.⟪ w ⟫

  -- The box with the colours γ, δ on the wires 1, 2.
  bx : Bool → Bool → Circuit N
  bx γ δ = N₁ᵇ γ (N₂ᵇ δ Box₃)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    pass : ∀ {a x y : Circuit N} → a • x ≈ x • a → a • y ≈ y • a → a • (x • y) ≈ (x • y) • a
    pass {a} {x} {y} ex ey = begin
      a • (x • y)   ≈⟨ sym assoc ⟩
      (a • x) • y   ≈⟨ front _ ex ⟩
      (x • a) • y   ≈⟨ assoc ⟩
      x • (a • y)   ≈⟨ back _ ey ⟩
      x • (y • a)   ≈⟨ sym assoc ⟩
      (x • y) • a ∎

    --------------------------------------------------------------------
    -- ZX₃ passes the four

    C₃ : Circuit N
    C₃ = place 2 (Λ□ (₃₊ k))

    ZX₃-C₃ : ZX₃ • C₃ ≈ C₃ • ZX₃
    ZX₃-C₃ = begin
      ZX₃ • C₃                   ≈⟨ back _ (sym (B₁₀↑-place k complete)) ⟩
      ZX₃ • B₁₀ (₁₊ k) ↑         ≈⟨ sym (eq291 k complete) ⟩
      B₁₀ (₁₊ k) ↑ • ZX₃         ≈⟨ front _ (B₁₀↑-place k complete) ⟩
      C₃ • ZX₃ ∎

    Box-S : S₂₃.⟪ C₃ ⟫ ≈ Box₃
    Box-S = sym (Eq.subst₂ (λ a b → a ≈ Ex ↑ ↑ • b • Ex ↑ ↑)
                  (placeAt-place 3 (Λ□ (₃₊ k))) (placeAt-place 2 (Λ□ (₃₊ k)))
                  (placeAt-step 2 (Λ□ (₃₊ k)) (s≤s (s≤s (s≤s z≤n)))))

    ZX₃-Box₃ : ZX₃ • Box₃ ≈ Box₃ • ZX₃
    ZX₃-Box₃ = S₂₃.⟪⟫-≈ ZX₃-C₃ (S₂₃.⟪⟫-•₂ fix Box-S) (S₂₃.⟪⟫-•₂ Box-S fix)
      where
      fix : S₂₃.⟪ ZX₃ ⟫ ≈ ZX₃
      fix = S₂₃.⟪⟫-fix (sym eq214)

    C′-B□↑ : C′ ≈ B□ k ↑
    C′-B□↑ = trans (lemma-5-1 3 complete (sem-C₀-yB k)) (place-yB k)

    ZX₃-C′ : ZX₃ • C′ ≈ C′ • ZX₃
    ZX₃-C′ = begin
      ZX₃ • C′         ≈⟨ back _ C′-B□↑ ⟩
      ZX₃ • B□ k ↑     ≈⟨ sym (eq290 k complete) ⟩
      B□ k ↑ • ZX₃     ≈⟨ front _ (sym C′-B□↑) ⟩
      C′ • ZX₃ ∎

    β₂-S : S₁₂.⟪ C′ ⟫ ≈ β₂
    β₂-S = sym (begin
      place 3 (Ex ↑ • C₀ k • Ex ↑)
        ≈⟨ trans (place-• 3 (Ex ↑) (C₀ k • Ex ↑)) (back _ (place-• 3 (C₀ k) (Ex ↑))) ⟩
      place 3 (Ex ↑) • C′ • place 3 (Ex ↑)
        ≈⟨ cong (place-low 3 (Ex {0} ↑)) (back _ (place-low 3 (Ex {0} ↑))) ⟩
      Ex ↑ • C′ • Ex ↑ ∎)

    ZX₃-β₂ : ZX₃ • β₂ ≈ β₂ • ZX₃
    ZX₃-β₂ = S₁₂.⟪⟫-≈ ZX₃-C′ (S₁₂.⟪⟫-•₂ fix β₂-S) (S₁₂.⟪⟫-•₂ β₂-S fix)
      where
      fix : S₁₂.⟪ ZX₃ ⟫ ≈ ZX₃
      fix = S₁₂.⟪⟫-fix (sym eq215)

    --------------------------------------------------------------------
    -- One width down, wire 3 idle: the colours as products

    module I = Forms (₁₊ k)

    Λ₄ : Circuit (₄₊ k)
    Λ₄ = Λ□ (₃₊ k)

    x₁ : CF {3} {₁₊ k} (X ↑)
    x₁ = cf-loc (X {1} ↑)

    x₂ : CF {3} {₁₊ k} (X ↑ ↑)
    x₂ = cf-loc (X {0} ↑ ↑)

    ex₁₂ : CF {3} {₁₊ k} (Ex ↑)
    ex₁₂ = cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def

    c₀ : CF {3} {₁₊ k} (C₀ k)
    c₀ = cf-• (cf-• (cf-• I.eps ex₁₂) I.ex) (cf-• (cf-Λ↑ k) (cf-• I.ex (cf-• ex₁₂ I.eps)))

    b₂ : CF {3} {₁₊ k} (Ex ↑ • C₀ k • Ex ↑)
    b₂ = cf-• ex₁₂ (cf-• c₀ ex₁₂)

    b∅ : CF {3} {₁₊ k} (Λ□ (₁₊ k) ↑ ↑)
    b∅ = cf-↑ (cf-↑ (cf-box 0 (₁₊ k)))

    n₂Λ : CF {3} {₁₊ k} (X ↑ ↑ • Λ₄ • X ↑ ↑)
    n₂Λ = cf-• x₂ (cf-• I.box x₂)

    s10 : ⟦ X ↑ ↑ • Λ₄ • X ↑ ↑ ⟧ ~ ⟦ C₀ k • Λ₄ ⟧
    s10 = cf-~ n₂Λ (cf-• c₀ I.box) Eq.refl Eq.refl

    s01 : ⟦ X ↑ • Λ₄ • X ↑ ⟧ ~ ⟦ (Ex ↑ • C₀ k • Ex ↑) • Λ₄ ⟧
    s01 = cf-~ (cf-• x₁ (cf-• I.box x₁)) (cf-• b₂ I.box) Eq.refl Eq.refl

    s00 : ⟦ X ↑ • (X ↑ ↑ • Λ₄ • X ↑ ↑) • X ↑ ⟧ ~
          ⟦ Λ□ (₁₊ k) ↑ ↑ • C₀ k • (Ex ↑ • C₀ k • Ex ↑) • Λ₄ ⟧
    s00 = cf-~ (cf-• x₁ (cf-• n₂Λ x₁)) (cf-• b∅ (cf-• c₀ (cf-• b₂ I.box))) Eq.refl Eq.refl

    -- X on the wires 1 2 through place 3.
    X₁-place : ∀ (u : Circuit (₄₊ k)) → X ↑ • place 3 u • X ↑ ≈ place 3 (X ↑ • u • X ↑)
    X₁-place u = sym (trans (place-• 3 (X ↑) (u • X ↑))
                   (cong (place-low 3 (X {1} ↑)) (trans (place-• 3 u (X ↑)) (back _ (place-low 3 (X {1} ↑))))))

    X₂-place : ∀ (u : Circuit (₄₊ k)) → X ↑ ↑ • place 3 u • X ↑ ↑ ≈ place 3 (X ↑ ↑ • u • X ↑ ↑)
    X₂-place u = sym (trans (place-• 3 (X ↑ ↑) (u • X ↑ ↑))
                   (cong (place-low 3 (X {0} ↑ ↑)) (trans (place-• 3 u (X ↑ ↑)) (back _ (place-low 3 (X {0} ↑ ↑))))))

    -- The coloured boxes as products of the four.
    bx10 : bx true false ≈ C′ • Box₃
    bx10 = begin
      X ↑ ↑ • Box₃ • X ↑ ↑                  ≈⟨ X₂-place Λ₄ ⟩
      place 3 (X ↑ ↑ • Λ₄ • X ↑ ↑)          ≈⟨ lemma-5-1 3 complete s10 ⟩
      place 3 (C₀ k • Λ₄)                   ≈⟨ place-• 3 (C₀ k) Λ₄ ⟩
      C′ • Box₃ ∎

    bx01 : bx false true ≈ β₂ • Box₃
    bx01 = begin
      X ↑ • Box₃ • X ↑                      ≈⟨ X₁-place Λ₄ ⟩
      place 3 (X ↑ • Λ₄ • X ↑)              ≈⟨ lemma-5-1 3 complete s01 ⟩
      place 3 ((Ex ↑ • C₀ k • Ex ↑) • Λ₄)   ≈⟨ place-• 3 (Ex ↑ • C₀ k • Ex ↑) Λ₄ ⟩
      β₂ • Box₃ ∎

    bx00 : bx false false ≈ β∅ k • C′ • β₂ • Box₃
    bx00 = begin
      X ↑ • (X ↑ ↑ • Box₃ • X ↑ ↑) • X ↑
        ≈⟨ back _ (front _ (X₂-place Λ₄)) ⟩
      X ↑ • place 3 (X ↑ ↑ • Λ₄ • X ↑ ↑) • X ↑
        ≈⟨ X₁-place (X ↑ ↑ • Λ₄ • X ↑ ↑) ⟩
      place 3 (X ↑ • (X ↑ ↑ • Λ₄ • X ↑ ↑) • X ↑)
        ≈⟨ lemma-5-1 3 complete s00 ⟩
      place 3 (Λ□ (₁₊ k) ↑ ↑ • C₀ k • (Ex ↑ • C₀ k • Ex ↑) • Λ₄)
        ≈⟨ trans (place-• 3 (Λ□ (₁₊ k) ↑ ↑) (C₀ k • (Ex ↑ • C₀ k • Ex ↑) • Λ₄))
            (back _ (trans (place-• 3 (C₀ k) ((Ex ↑ • C₀ k • Ex ↑) • Λ₄))
                           (back _ (place-• 3 (Ex ↑ • C₀ k • Ex ↑) Λ₄)))) ⟩
      β∅ k • C′ • β₂ • Box₃ ∎

  ----------------------------------------------------------------------
  -- (319)

  eq319 : ∀ γ δ → ZX₃ • bx γ δ ≈ bx γ δ • ZX₃
  eq319 true  true  = ZX₃-Box₃
  eq319 true  false = trans (back _ bx10) (trans (pass ZX₃-C′ ZX₃-Box₃) (front _ (sym bx10)))
  eq319 false true  = trans (back _ bx01) (trans (pass ZX₃-β₂ ZX₃-Box₃) (front _ (sym bx01)))
  eq319 false false = trans (back _ bx00)
    (trans (pass (ZX₃-β∅ k below) (pass ZX₃-C′ (pass ZX₃-β₂ ZX₃-Box₃))) (front _ (sym bx00)))

  -- And its inverse XZ₃; and both, as rot.
  eq319′ : ∀ γ δ → XZ₃ • bx γ δ ≈ bx γ δ • XZ₃
  eq319′ γ δ = sym (comm-inv eq208′ eq208 (sym (eq319 γ δ)))

  eq319-rot : ∀ a γ δ → rot a • bx γ δ ≈ bx γ δ • rot a
  eq319-rot false = eq319′
  eq319-rot true  = eq319
