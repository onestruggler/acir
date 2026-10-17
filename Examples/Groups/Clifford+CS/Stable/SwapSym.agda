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
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
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
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ ; Swᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Split using (Sw²)
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
