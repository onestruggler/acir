------------------------------------------------------------------------
-- Presentations of groups
--
-- The symmetry of two white controls, for twisted commutators
--
-- Stable.Gadget needs, from six wires on, that λ⁰ λ⁰ of the gadget does
-- not see the order of its two controls (`SwapSym`).  The gadgets are
-- twisted commutators — P ≈ G⁻ U⁻ G U with G⁻ G inverse and U a gate on
-- wire 0 (Five.Facts4's dec-pp⁻, dec-ki⁻) — and that survives λ⁰ with
-- the gate U left uncontrolled (`tw-step`, CalcW.tw-top′).  Under λ⁰ λ⁰
-- the gadget factors then lose both controls (CalcW.tw-top, twice):
--
--     λ⁰ λ⁰ P ≈ top top G⁻ • λ⁰ λ⁰ U⁻ • top top G • λ⁰ λ⁰ U,
--
-- and the exchange of the two top wires passes a circuit idle on both
-- (`sw-tt`, by the structural rules).  So SwapSym for P follows from
-- SwapSym for the doubly controlled gate U on wire 0 (`swapsym-tw`), and
-- SwapSym is closed under products and inverses (`ss-•`, `ss-inv`).
-- With X on both controls the white λ⁰ λ⁰ w is the black λ¹ λ¹ w
-- (`λ⁰λ⁰-X`), and the exchange swaps the two X, so SwapSym for λ¹ λ¹ w
-- gives it for λ⁰ λ⁰ w (`ss-λ⁰λ⁰`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)

module Examples.Groups.Clifford+CS.Stable.SwapSym
  (m : ℕ)
  (f4₀ : F4ᵗ m) (f5₀ : F5ᵗ m)
  (tr₀ : ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (f4₁ : F4ᵗ (suc m)) (f5₁ : F5ᵗ (suc m))
  (tr₁ : ∀ {u v : Circuit (₄₊ (suc m))} → (₄₊ (suc m)) ⊢ᵧ u ≈ v → (suc (₄₊ (suc m))) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₂₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ ; Swᵗ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Split using (Sw² ; top-↑)
open import Examples.Groups.Clifford+CS.Stable.Mixed using (Xᵗ²)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (top-congᵧ)
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW

private
  D W W′ : ℕ
  D  = ₄₊ m
  W  = suc (₄₊ m)
  W′ = suc (suc (₄₊ m))

  module CW₀ = CalcW m f4₀ f5₀ tr₀
  module CW₁ = CalcW (suc m) f4₁ f5₁ tr₁

------------------------------------------------------------------------
-- The exchange of the top two wires passes a circuit idle on both

private
  sw-g : ∀ n (g : Gen n) → (₂₊ n) ⊢ Swᵗ n • [ (g ↧) ↧ ]ʷ ≈ [ (g ↧) ↧ ]ʷ • Swᵗ n
  sw-g n             (gate₀ h) = comm-gate₀-w h (Swᵗ n)
  sw-g (suc n)       (gate₁ h) = comm-gate₁-w↑ h (Swᵗ n)
  sw-g (suc (suc n)) (gate₂ h) = comm-gate₂-w↑↑ h (Swᵗ n)
  sw-g (suc n)       (g ↥)     = lemma-cong↑ (Swᵗ n • [ (g ↧) ↧ ]ʷ) ([ (g ↧) ↧ ]ʷ • Swᵗ n) (sw-g n g)

sw-tt : ∀ n (w : Circuit n) → (₂₊ n) ⊢ Swᵗ n • top (top w) ≈ top (top w) • Swᵗ n
sw-tt n [ g ]ʷ  = sw-g n g
sw-tt n ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
sw-tt n (u • v) =
  PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (sw-tt n u) PB.refl)
    (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (sw-tt n v)) (PB.sym PB.assoc))))

------------------------------------------------------------------------
-- The symmetry, as passing the exchange

private
  Sw : Circuit W′
  Sw = Swᵗ (₄₊ m)

  open Tools (W′ YVRel,_===_)

  ss : W′ ⊢ᵧ Sw • Sw ≈ ε
  ss = embed (Sw² (₄₊ m))

-- y does not see the order of the two top wires.
SS : Circuit W′ → Set
SS y = W′ ⊢ᵧ Sw • y • Sw ≈ y

private
  Pass : Circuit W′ → Set
  Pass y = W′ ⊢ᵧ Sw • y ≈ y • Sw

  ss→pass : ∀ {y} → SS y → Pass y
  ss→pass {y} s = begin
    Sw • y                  ≈⟨ sym right-unit ⟩
    (Sw • y) • ε            ≈⟨ back _ (sym ss) ⟩
    (Sw • y) • (Sw • Sw)    ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (Sw • y • Sw) • Sw      ≈⟨ front _ s ⟩
    y • Sw                  ∎

  pass→ss : ∀ {y} → Pass y → SS y
  pass→ss {y} p = begin
    Sw • y • Sw             ≈⟨ sym assoc ⟩
    (Sw • y) • Sw           ≈⟨ front _ p ⟩
    (y • Sw) • Sw           ≈⟨ assoc ⟩
    y • (Sw • Sw)           ≈⟨ back _ ss ⟩
    y • ε                   ≈⟨ right-unit ⟩
    y                       ∎

  pass-• : ∀ {a b} → Pass a → Pass b → Pass (a • b)
  pass-• {a} {b} pa pb = begin
    Sw • (a • b)            ≈⟨ sym assoc ⟩
    (Sw • a) • b            ≈⟨ front _ pa ⟩
    (a • Sw) • b            ≈⟨ assoc ⟩
    a • (Sw • b)            ≈⟨ back _ pb ⟩
    a • (b • Sw)            ≈⟨ sym assoc ⟩
    (a • b) • Sw            ∎

  pass≈ : ∀ {x y} → W′ ⊢ᵧ x ≈ y → Pass x → Pass y
  pass≈ e p = trans (back _ (sym e)) (trans p (front _ e))

ss-• : ∀ {a b} → SS a → SS b → SS (a • b)
ss-• sa sb = pass→ss (pass-• (ss→pass sa) (ss→pass sb))

ss-inv : ∀ {x y} → SS x → W′ ⊢ᵧ x • y ≈ ε → W′ ⊢ᵧ y • x ≈ ε → SS y
ss-inv {x} {y} sx xy yx = pass→ss (begin
  Sw • y                    ≈⟨ sym left-unit ⟩
  ε • Sw • y                ≈⟨ front _ (sym yx) ⟩
  (y • x) • Sw • y          ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  y • (x • Sw) • y          ≈⟨ back y (front y (sym (ss→pass sx))) ⟩
  y • (Sw • x) • y          ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  y • Sw • (x • y)          ≈⟨ back y (back Sw xy) ⟩
  y • Sw • ε                ≈⟨ back y right-unit ⟩
  y • Sw                    ∎)

------------------------------------------------------------------------
-- Twisted commutators

-- A twisted commutator stays one under λ⁰, with its gate uncontrolled.
tw-step : ∀ (P Gm Gp U Um : Circuit D) → D ⊢ᵧ P ≈ Gm • Um • Gp • U →
          D ⊢ᵧ U • Um ≈ ε → D ⊢ᵧ Um • U ≈ ε →
          W ⊢ᵧ λ⁰ʷ P ≈ λ⁰ʷ Gm • top Um • λ⁰ʷ Gp • top U
tw-step P Gm Gp U Um eP e e′ = PB.trans (CW₀.transport⁰ eP) (CW₀.tw-top′ Gp Gm U Um e e′)

-- Under λ⁰ λ⁰ its two gadget factors lose both controls.
tw-tt : ∀ (P Gm Gp U Um : Circuit D) → D ⊢ᵧ P ≈ Gm • Um • Gp • U →
        D ⊢ᵧ Gp • Gm ≈ ε → D ⊢ᵧ Gm • Gp ≈ ε →
        W′ ⊢ᵧ λ⁰ʷ (λ⁰ʷ P) ≈ top (top Gm) • λ⁰ʷ (λ⁰ʷ Um) • top (top Gp) • λ⁰ʷ (λ⁰ʷ U)
tw-tt P Gm Gp U Um eP pm mp =
  PB.trans (CW₁.transport⁰ e₁)
    (CW₁.tw-top (top Gp) (top Gm) (λ⁰ʷ U) (λ⁰ʷ Um) (top-congᵧ pm) (top-congᵧ mp))
  where
  e₁ : W ⊢ᵧ λ⁰ʷ P ≈ top Gm • λ⁰ʷ Um • top Gp • λ⁰ʷ U
  e₁ = PB.trans (CW₀.transport⁰ eP) (CW₀.tw-top Gp Gm U Um pm mp)

-- SwapSym for a twisted commutator from SwapSym for its gate.
swapsym-tw : ∀ (P Gm Gp U Um : Circuit D) → D ⊢ᵧ P ≈ Gm • Um • Gp • U →
             D ⊢ᵧ Gp • Gm ≈ ε → D ⊢ᵧ Gm • Gp ≈ ε →
             SS (λ⁰ʷ (λ⁰ʷ U)) → SS (λ⁰ʷ (λ⁰ʷ Um)) → SS (λ⁰ʷ (λ⁰ʷ P))
swapsym-tw P Gm Gp U Um eP pm mp sU sUm =
  pass→ss (pass≈ (sym (tw-tt P Gm Gp U Um eP pm mp))
    (pass-• (embed (sw-tt (₄₊ m) Gm))
      (pass-• (ss→pass sUm) (pass-• (embed (sw-tt (₄₊ m) Gp)) (ss→pass sU)))))

------------------------------------------------------------------------
-- White controls from black ones

private
  module S₂ = Below 2 complete₂

  ≡→≈₀ : ∀ {n} {a b : Circuit n} → a ≡ b → n ⊢ a ≈ b
  ≡→≈₀ Eq.refl = PB.refl

  -- The exchange of the top two wires moves X from one to the other.
  swX : ∀ k → (₂₊ k) ⊢ Swᵗ k • top (Xᵗ k) • Swᵗ k ≈ Xᵗ (suc k)
  swX zero    = S₂.by-sem₀ (Swap • X • Swap) (X ↑) Eq.refl
  swX (suc k) =
    PB.trans (PB.cong PB.refl (PB.cong (≡→≈₀ (top-↑ (Xᵗ k))) PB.refl))
             (lemma-cong↑ (Swᵗ k • top (Xᵗ k) • Swᵗ k) (Xᵗ (suc k)) (swX k))

  -- X on the two top wires commute.
  xx-comm : ∀ k → (₂₊ k) ⊢ top (Xᵗ k) • Xᵗ (suc k) ≈ Xᵗ (suc k) • top (Xᵗ k)
  xx-comm zero    = S₂.by-sem₀ (X • X ↑) (X ↑ • X) Eq.refl
  xx-comm (suc k) =
    PB.trans (PB.cong (≡→≈₀ (top-↑ (Xᵗ k))) PB.refl)
      (PB.trans (lemma-cong↑ (top (Xᵗ k) • Xᵗ (suc k)) (Xᵗ (suc k) • top (Xᵗ k)) (xx-comm k))
                (PB.cong PB.refl (≡→≈₀ (Eq.sym (top-↑ (Xᵗ k))))))

  x₁ : Circuit W
  x₁ = Xᵗ (₄₊ m)

  x₂ : Circuit W′
  x₂ = Xᵗ (suc (₄₊ m))

-- λ⁰ λ⁰ is λ¹ λ¹ between X on both controls.
λ⁰λ⁰-X : ∀ (w : Circuit D) → W′ ⊢ᵧ λ⁰ʷ (λ⁰ʷ w) ≈ top x₁ • x₂ • λ¹ʷ (λ¹ʷ w) • x₂ • top x₁
λ⁰λ⁰-X w = begin
  λ⁰ʷ (λ⁰ʷ w)                                   ≈⟨ CW₁.transport⁰ (CW₀.λ⁰-X w) ⟩
  λ⁰ʷ (x₁ • λ¹ʷ w • x₁)                         ≈⟨ sym (CW₁.conj⁰ x₁ x₁ (λ¹ʷ w) (embed (Xᵗ² (₄₊ m)))) ⟩
  top x₁ • λ⁰ʷ (λ¹ʷ w) • top x₁                 ≈⟨ back _ (front _ (CW₁.λ⁰-X (λ¹ʷ w))) ⟩
  top x₁ • (x₂ • λ¹ʷ (λ¹ʷ w) • x₂) • top x₁     ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  top x₁ • x₂ • λ¹ʷ (λ¹ʷ w) • x₂ • top x₁       ∎

private
  -- x turns into y under the exchange.
  Tw : Circuit W′ → Circuit W′ → Set
  Tw x y = W′ ⊢ᵧ Sw • x ≈ y • Sw

  tw : ∀ {x y} → W′ ⊢ᵧ Sw • x • Sw ≈ y → Tw x y
  tw {x} {y} s = begin
    Sw • x                  ≈⟨ sym right-unit ⟩
    (Sw • x) • ε            ≈⟨ back _ (sym ss) ⟩
    (Sw • x) • (Sw • Sw)    ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (Sw • x • Sw) • Sw      ≈⟨ front _ s ⟩
    y • Sw                  ∎

  tw-• : ∀ {x y x′ y′} → Tw x y → Tw x′ y′ → Tw (x • x′) (y • y′)
  tw-• {x} {y} {x′} {y′} p q = begin
    Sw • (x • x′)           ≈⟨ sym assoc ⟩
    (Sw • x) • x′           ≈⟨ front _ p ⟩
    (y • Sw) • x′           ≈⟨ assoc ⟩
    y • (Sw • x′)           ≈⟨ back _ q ⟩
    y • (y′ • Sw)           ≈⟨ sym assoc ⟩
    (y • y′) • Sw           ∎

  -- And back.
  unsw : ∀ {x y} → W′ ⊢ᵧ Sw • x • Sw ≈ y → W′ ⊢ᵧ Sw • y • Sw ≈ x
  unsw {x} {y} s = begin
    Sw • y • Sw                   ≈⟨ back _ (front _ (sym s)) ⟩
    Sw • (Sw • x • Sw) • Sw       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (Sw • Sw) • x • (Sw • Sw)     ≈⟨ cong ss (back x ss) ⟩
    ε • x • ε                     ≈⟨ trans left-unit right-unit ⟩
    x                             ∎

-- SwapSym for λ⁰ λ⁰ w from SwapSym for λ¹ λ¹ w.
ss-λ⁰λ⁰ : ∀ (w : Circuit D) → SS (λ¹ʷ (λ¹ʷ w)) → SS (λ⁰ʷ (λ⁰ʷ w))
ss-λ⁰λ⁰ w sc = pass→ss (pass≈ (sym (λ⁰λ⁰-X w)) (trans t (front Sw reorder)))
  where
  a = top x₁
  b = x₂
  c = λ¹ʷ (λ¹ʷ w)
  ab : W′ ⊢ᵧ Sw • a • Sw ≈ b
  ab = embed (swX (₄₊ m))
  t : Tw (a • b • c • b • a) (b • a • c • a • b)
  t = tw-• (tw ab) (tw-• (tw (unsw ab)) (tw-• (ss→pass sc) (tw-• (tw (unsw ab)) (tw ab))))
  comm : W′ ⊢ᵧ a • b ≈ b • a
  comm = embed (xx-comm (₄₊ m))
  reorder : W′ ⊢ᵧ b • a • c • a • b ≈ a • b • c • b • a
  reorder = begin
    b • a • c • a • b             ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (b • a) • c • (a • b)         ≈⟨ cong (sym comm) (back c comm) ⟩
    (a • b) • c • (b • a)         ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • □ • □ • □ • □) Eq.refl ⟩
    a • b • c • b • a             ∎
