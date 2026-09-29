------------------------------------------------------------------------
-- Presentations of groups
--
-- The box against the H gate with the same box wire, of the other
-- colour on wire 2 (Clément, Lemma D.13, Equation (337))
--
-- At width 5 + k: the box on wire 0 commutes with the H gate on wire 1
-- whose box wire is wire 0 (ΛH), white on wire 2 (`eq337`).
-- Semantically the box acts only where wire 2 is 1 and the H gate only
-- where it is 0.  As for (339) (GeneralN.Box339), there is no induction:
-- both gates are expanded by (320) — the H gate as the box between P ⊗ P
-- on the wires 0 1 and X on wire 2 — and every letter of one passes
-- every letter of the other:
--
--   * two rotations: decided on four wires (Base337) and weakened;
--   * a rotation of one against the smaller box of the other: between
--     P ⊗ P and X on wire 2 this is (322) (GeneralN.Gadget322), with the
--     box wire on wire 0 or, under the swap of the wires 0 1, on wire 1;
--   * the two smaller boxes: both leave wire 3 idle, so one width down
--     it is a step decided on the controlled forms (`sem-bb`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box337
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111 ; eq112)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (module Aj)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm using (CF ; cf-• ; cf-~ ; cf-loc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (module Forms)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-cong ; place-low ; lemma-5-1 ; low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; col-Ex ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Vb ; bot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget322 complete₂ complete₃
  using (L ; zx ; xz ; kb ; kb′ ; bb ; lt ; es ; word ; via ; module CW ; E320 ; Gd ; gd ; S-place ;
         ZX-XZ ; XZ-ZX ; K-K′ ; K′-K)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (all-pairs ; module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (N₂-place ; X₂²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base337 using (U₄ ; G2 ; d337r)

------------------------------------------------------------------------
-- The two smaller boxes, one width down: decided on the controlled forms

module _ (k : ℕ) where
  open Forms k

  private
    x₂ : CF {3} {k} (X ↑ ↑)
    x₂ = cf-loc (X {0} ↑ ↑)

    a′ : CF {3} {k} (X ↑ ↑ • (PP ↓ • Λ□ (₂₊ k) • PP ↓) • X ↑ ↑)
    a′ = cf-• x₂ (cf-• (cf-• pp (cf-• box pp)) x₂)

  sem-bb : ⟦ Λ□ (₂₊ k) • (X ↑ ↑ • (PP ↓ • Λ□ (₂₊ k) • PP ↓) • X ↑ ↑) ⟧ ~
           ⟦ (X ↑ ↑ • (PP ↓ • Λ□ (₂₊ k) • PP ↓) • X ↑ ↑) • Λ□ (₂₊ k) ⟧
  sem-bb = cf-~ (cf-• box a′) (cf-• a′ box) Eq.refl Eq.refl

------------------------------------------------------------------------
-- Colourings and placements at width 4 + j

module _ {j : ℕ} where
  open Tools ((₄₊ j) VRel,_===_)

  private
    ≡→≈ : ∀ {a b : Circuit (₄₊ j)} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  -- White on wire 2 and black elsewhere is X on wire 2.
  col-2 : ∀ (w : Circuit (₄₊ j)) → col (true ∷ true ∷ false ∷ replicate (₁₊ j) true) w ≈ X ↑ ↑ • w • X ↑ ↑
  col-2 w = trans (≡→≈ (Eq.cong (λ z → ((X • z ↑) ↑ ↑) • w • ((X • z ↑) ↑ ↑)) (allT (₁₊ j))))
                  (cong right-unit (back _ right-unit))

  col-2′ : ∀ (w : Circuit (₄₊ j)) → X ↑ ↑ • w • X ↑ ↑ ≈ col (true ∷ true ∷ false ∷ replicate (₁₊ j) true) w
  col-2′ w = sym (col-2 w)

module _ {r : ℕ} where
  open Tools ((₄₊ r) VRel,_===_)

  -- P ⊗ P on the wires 0 1 through a placement around wire 3.
  Aj-place : ∀ (V : Circuit (₃₊ r)) → Aj.⟪ place 3 V ⟫ ≈ place 3 (PP ↓ • V • PP ↓)
  Aj-place V = sym (trans (place-• 3 (PP ↓) (V • PP ↓))
                 (cong (place-low 3 (PP {1})) (trans (place-• 3 V (PP ↓)) (back _ (place-low 3 (PP {1}))))))

------------------------------------------------------------------------
-- (337) at width 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)

  private
    Λ′ : Circuit (₄₊ k)
    Λ′ = Λ□ (₃₊ k)

    module CN = Carry {N} (X ↑ ↑) X₂²
    module CP = Carry {N} (PP ↓) eq111
    module CS = Carry {N} (Ex ↓) Ex²

    ones : Bits (₁₊ k)
    ones = replicate (₁₊ k) true

    F₂ : Circuit N → Circuit N
    F₂ w = N₂.⟪ Aj.⟪ w ⟫ ⟫

    f₁ f₂ : L → Circuit N
    f₁ l = lt (suc k) l
    f₂ l = F₂ (lt (suc k) l)

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p′ • q′ ≈ q′ • p′ → p • q ≈ q • p
    both ep eq e = trans (cong ep eq) (trans e (sym (cong eq ep)))

    -- The two gates as words in their letters.
    G₁-word : Λ□ (₄₊ k) ≈ word f₁ es
    G₁-word = E320 c₄ (suc k) below

    G₂-word : X ↑ ↑ • ΛH (₃₊ k) • X ↑ ↑ ≈ word f₂ es
    G₂-word = trans (N₂.⟪⟫-cong (trans (Aj.⟪⟫-cong (E320 c₄ (suc k) below))
                                        (CW.⟪⟫-word (PP ↓) eq111 (lt (suc k)) es)))
                    (CW.⟪⟫-word (X ↑ ↑) X₂² (λ l → Aj.⟪ lt (suc k) l ⟫) es)

    --------------------------------------------------------------------
    -- The conjugations commute

    N₂A : ∀ (w : Circuit N) → N₂.⟪ Aj.⟪ w ⟫ ⟫ ≈ Aj.⟪ N₂.⟪ w ⟫ ⟫
    N₂A w = conj-swap (sym (low-comm PP X)) w

    SA : ∀ (w : Circuit N) → S₀₁.⟪ Aj.⟪ w ⟫ ⟫ ≈ Aj.⟪ S₀₁.⟪ w ⟫ ⟫
    SA w = conj-swap (sym eq112) w

    --------------------------------------------------------------------
    -- The smaller box, white on wire 2, with its box wire on wire 0 or 1

    G G′ : Circuit N
    G  = place 3 (col (bot true true ones) (Vb true (suc k)))
    G′ = place 3 (col (bot false true ones) (Vb false (suc k)))

    N₂-bb : N₂.⟪ place 3 Λ′ ⟫ ≈ G
    N₂-bb = trans (N₂-place Λ′) (place-cong 3 (col-2′ Λ′))

    S-G : S₀₁.⟪ G ⟫ ≈ G′
    S-G = trans (S-place _) (place-cong 3 (col-Ex (bot true true ones) Λ′))

    f₂-bb : f₂ bb ≈ Aj.⟪ G ⟫
    f₂-bb = trans (N₂A (place 3 Λ′)) (Aj.⟪⟫-cong N₂-bb)

    gd′ : Gd (suc k)
    gd′ = gd c₄ (suc k) below

    --------------------------------------------------------------------
    -- A rotation against the smaller box: (322) between P ⊗ P and X on
    -- wire 2

    zx-G : ZX₃ • Aj.⟪ G ⟫ ≈ Aj.⟪ G ⟫ • ZX₃
    zx-G = CP.carry (unconj eq111) refl (gd′ true true true true ones true)

    zx-G′ : ZX₃ • Aj.⟪ G′ ⟫ ≈ Aj.⟪ G′ ⟫ • ZX₃
    zx-G′ = CP.carry (unconj eq111) refl (gd′ true true true true ones false)

    zx-bb : f₁ zx • f₂ bb ≈ f₂ bb • f₁ zx
    zx-bb = via f₂-bb zx-G

    kb-bb : f₁ kb • f₂ bb ≈ f₂ bb • f₁ kb
    kb-bb = via f₂-bb (CS.carry refl (trans (SA G′) (Aj.⟪⟫-cong (conj-sym Ex² S-G))) zx-G′)

    bb-zx : f₁ bb • f₂ zx ≈ f₂ zx • f₁ bb
    bb-zx = CN.carry (conj-sym X₂² N₂-bb) refl (sym (gd′ true true true true ones true))

    bb-kb : f₁ bb • f₂ kb ≈ f₂ kb • f₁ bb
    bb-kb = CN.carry (conj-sym X₂² N₂-bb) refl
              (CS.carry (conj-sym Ex² S-G) (SA ZX₃) (sym (gd′ true true true true ones false)))

    --------------------------------------------------------------------
    -- The two smaller boxes: one width down, wire 3 idle

    bb-bb : f₁ bb • f₂ bb ≈ f₂ bb • f₁ bb
    bb-bb = via f₂-pl (begin
      place 3 Λ′ • place 3 A′     ≈⟨ sym (place-• 3 _ _) ⟩
      place 3 (Λ′ • A′)           ≈⟨ lemma-5-1 3 c (sem-bb (₁₊ k)) ⟩
      place 3 (A′ • Λ′)           ≈⟨ place-• 3 _ _ ⟩
      place 3 A′ • place 3 Λ′ ∎)
      where
      A′ : Circuit (₄₊ k)
      A′ = X ↑ ↑ • (PP ↓ • Λ′ • PP ↓) • X ↑ ↑
      f₂-pl : f₂ bb ≈ place 3 A′
      f₂-pl = trans (N₂.⟪⟫-cong (Aj-place Λ′)) (N₂-place (PP ↓ • Λ′ • PP ↓))

    --------------------------------------------------------------------
    -- Two rotations: decided on four wires

    rr : ∀ b c′ → (U₄ b ↓ᵏ (₁₊ k)) • (G2 c′ ↓ᵏ (₁₊ k)) ≈ (G2 c′ ↓ᵏ (₁₊ k)) • (U₄ b ↓ᵏ (₁₊ k))
    rr b c′ = by-sem (U₄ b • G2 c′) (G2 c′ • U₄ b) (Evaluated.same (d337r b c′)) {₁₊ k}

    --------------------------------------------------------------------
    -- Inverses

    inv₂ : ∀ {u v : Circuit N} → u • v ≈ ε → F₂ u • F₂ v ≈ ε
    inv₂ {u} {v} e = trans (sym (N₂.⟪⟫-• (Aj.⟪ u ⟫) (Aj.⟪ v ⟫)))
                       (trans (N₂.⟪⟫-cong (trans (sym (Aj.⟪⟫-• u v)) (trans (Aj.⟪⟫-cong e) Aj.⟪⟫-ε))) N₂.⟪⟫-ε)

    right : ∀ {Y u v} → u • v ≈ ε → v • u ≈ ε → Y • F₂ u ≈ F₂ u • Y → Y • F₂ v ≈ F₂ v • Y
    right uv vu e = comm-inv (inv₂ uv) (inv₂ vu) e

    left : ∀ {Y w v} → w • v ≈ ε → v • w ≈ ε → w • Y ≈ Y • w → v • Y ≈ Y • v
    left wv vw e = sym (comm-inv wv vw (sym e))

    --------------------------------------------------------------------
    -- Every pair

    rZ : ∀ l′ → f₁ zx • f₂ l′ ≈ f₂ l′ • f₁ zx
    rZ zx  = rr true true
    rZ kb  = rr true false
    rZ xz  = right ZX-XZ XZ-ZX (rZ zx)
    rZ kb′ = right K-K′ K′-K (rZ kb)
    rZ bb  = zx-bb

    rK : ∀ l′ → f₁ kb • f₂ l′ ≈ f₂ l′ • f₁ kb
    rK zx  = rr false true
    rK kb  = rr false false
    rK xz  = right ZX-XZ XZ-ZX (rK zx)
    rK kb′ = right K-K′ K′-K (rK kb)
    rK bb  = kb-bb

    rB : ∀ l′ → f₁ bb • f₂ l′ ≈ f₂ l′ • f₁ bb
    rB zx  = bb-zx
    rB kb  = bb-kb
    rB xz  = right ZX-XZ XZ-ZX bb-zx
    rB kb′ = right K-K′ K′-K bb-kb
    rB bb  = bb-bb

    pair : ∀ l l′ → f₁ l • f₂ l′ ≈ f₂ l′ • f₁ l
    pair zx  l′ = rZ l′
    pair kb  l′ = rK l′
    pair xz  l′ = left ZX-XZ XZ-ZX (rZ l′)
    pair kb′ l′ = left K-K′ K′-K (rK l′)
    pair bb  l′ = rB l′

  ----------------------------------------------------------------------
  -- (337)

  eq337 : Λ□ (₄₊ k) • (X ↑ ↑ • ΛH (₃₊ k) • X ↑ ↑) ≈ (X ↑ ↑ • ΛH (₃₊ k) • X ↑ ↑) • Λ□ (₄₊ k)
  eq337 = both G₁-word G₂-word (all-pairs f₁ f₂ es es pair)
