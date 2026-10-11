------------------------------------------------------------------------
-- Presentations of groups
--
-- The CH from a control onto the box wire passes the box, and the box
-- is an involution (Clément, Lemma D.8, Equations (297)–(299))
--
-- With the box in its E-form W • E • V • E, (284), these are short.
-- Conjugation by the CH from wire 1 onto wire 0 exchanges the doubly
-- controlled ZX and XZ, W and V (three wires), and fixes the
-- multi-controlled H, E (one width down with wire 2 idle: both are H on
-- wire 0, under disjoint controls); so it carries W E V E to V E W E,
-- which is the box again by (284)'s mirror — (298).  With the control
-- white it fixes W and V as well, and the E-form itself is carried to
-- itself — (297).
--
-- (299) is then the paper's argument, shortened: V = CZ₂₀ • CH • CZ₂₀ • CH
-- passes the box factor by factor, by (273) and (298), and between the
-- B-form (269) and its mirror (286) the box squared is
-- (V W) B (V W) B = B B = ε, B being an involution one width down.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; ax)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq273 ; eq286)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; E□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (HG₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemFull using (sem-HG-CH ; sem-HG-°CH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place-low)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃
  using (eq284 ; eq284′ ; B□² ; place-E□ ; commute-placed)

Eq297 Eq298 Eq299 : ℕ → Set
Eq297 k = (₄₊ k) ⊢ °CH • Λ□ (₃₊ k) ≈ Λ□ (₃₊ k) • °CH
Eq298 k = (₄₊ k) ⊢ CH • Λ□ (₃₊ k) ≈ Λ□ (₃₊ k) • CH
Eq299 k = (₄₊ k) ⊢ Λ□ (₃₊ k) • Λ□ (₃₊ k) ≈ ε

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    Λ W V E B : Circuit (₄₊ k)
    Λ = Λ□ (₃₊ k)
    W = CCZX
    V = CCXZ
    E = E□ k
    B = B□ k

    CH² : (₄₊ k) ⊢ CH • CH ≈ ε
    CH² = ax order-CH

    °CH² : (₄₊ k) ⊢ °CH • °CH ≈ ε
    °CH² = L₃-sem (°CH • °CH) ε Eq.refl

    module C = Conj {₄₊ k} CH CH²
    module C° = Conj {₄₊ k} °CH °CH²

    -- Three wires.
    CH-W : (₄₊ k) ⊢ CH • W • CH ≈ V
    CH-W = L₃-sem (CH • CCZX • CH) CCXZ Eq.refl

    CH-V : (₄₊ k) ⊢ CH • V • CH ≈ W
    CH-V = L₃-sem (CH • CCXZ • CH) CCZX Eq.refl

    °CH-W : (₄₊ k) ⊢ °CH • W • °CH ≈ W
    °CH-W = L₃-sem (°CH • CCZX • °CH) CCZX Eq.refl

    °CH-V : (₄₊ k) ⊢ °CH • V • °CH ≈ V
    °CH-V = L₃-sem (°CH • CCXZ • °CH) CCXZ Eq.refl

    V-W : (₄₊ k) ⊢ V • W ≈ ε
    V-W = L₃-sem (CCXZ • CCZX) ε Eq.refl

    -- A gate that passes w and is its own inverse fixes it.
    fix : ∀ {c w : Circuit (₄₊ k)} → (₄₊ k) ⊢ c • c ≈ ε → (₄₊ k) ⊢ w • c ≈ c • w →
          (₄₊ k) ⊢ c • w • c ≈ w
    fix {c} {w} e h = begin
      c • w • c       ≈⟨ back _ h ⟩
      c • c • w       ≈⟨ sym assoc ⟩
      (c • c) • w     ≈⟨ front _ e ⟩
      ε • w           ≈⟨ left-unit ⟩
      w ∎

    -- One width down with wire 2 idle.
    E-CH : (₄₊ k) ⊢ CH • E • CH ≈ E
    E-CH = fix CH² (commute-placed k complete {X = HG₀₁ k} {Y = CH} (place-E□ k complete) (place-low 2 CH) (sem-HG-CH k))

    E-°CH : (₄₊ k) ⊢ °CH • E • °CH ≈ E
    E-°CH = fix °CH² (commute-placed k complete {X = HG₀₁ k} {Y = °CH} (place-E□ k complete) (place-low 2 °CH) (sem-HG-°CH k))

    -- A gate fixed by an involution passes it.
    passes : ∀ {c w : Circuit (₄₊ k)} → (₄₊ k) ⊢ c • c ≈ ε → (₄₊ k) ⊢ c • w • c ≈ w →
             (₄₊ k) ⊢ c • w ≈ w • c
    passes e h = sym (conj-comm e h)

  ----------------------------------------------------------------------
  -- (298) and (297)

  eq298 : Eq298 k
  eq298 = passes CH² (begin
    CH • Λ • CH             ≈⟨ C.⟪⟫-cong (eq284 k complete) ⟩
    CH • (W • E • V • E) • CH ≈⟨ C.⟪⟫-•₄ CH-W E-CH CH-V E-CH ⟩
    V • E • W • E           ≈⟨ sym (eq284′ k complete) ⟩
    Λ ∎)

  eq297 : Eq297 k
  eq297 = passes °CH² (begin
    °CH • Λ • °CH             ≈⟨ C°.⟪⟫-cong (eq284 k complete) ⟩
    °CH • (W • E • V • E) • °CH ≈⟨ C°.⟪⟫-•₄ °CH-W E-°CH °CH-V E-°CH ⟩
    W • E • V • E             ≈⟨ sym (eq284 k complete) ⟩
    Λ ∎)

  ----------------------------------------------------------------------
  -- (299)

  private
    -- A product passing y passes it.
    pass′ : ∀ {a b y : Circuit (₄₊ k)} → (₄₊ k) ⊢ a • y ≈ y • a → (₄₊ k) ⊢ b • y ≈ y • b →
            (₄₊ k) ⊢ (a • b) • y ≈ y • (a • b)
    pass′ {a} {b} {y} ha hb = begin
      (a • b) • y     ≈⟨ assoc ⟩
      a • (b • y)     ≈⟨ back _ hb ⟩
      a • (y • b)     ≈⟨ sym assoc ⟩
      (a • y) • b     ≈⟨ front _ ha ⟩
      (y • a) • b     ≈⟨ assoc ⟩
      y • (a • b) ∎

    V-Λ : (₄₊ k) ⊢ V • Λ ≈ Λ • V
    V-Λ = pass′ (eq273 k) (pass′ eq298 (pass′ (eq273 k) eq298))

  eq299 : Eq299 k
  eq299 = begin
    Λ • Λ                               ≈⟨ back _ (eq286 k) ⟩
    Λ • (V • B • W • B)                 ≈⟨ sym assoc ⟩
    (Λ • V) • B • W • B                 ≈⟨ front _ (sym V-Λ) ⟩
    (V • Λ) • B • W • B                 ≈⟨ by-passoc ((□ • (□ • □ • □ • □)) • □ • □ • □)
                                                    ((□ • □) • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    (V • W) • B • V • (B • B) • W • B   ≈⟨ back _ (back _ (back _ (front _ (B□² k complete)))) ⟩
    (V • W) • B • V • ε • W • B         ≈⟨ back _ (back _ (back _ left-unit)) ⟩
    (V • W) • B • V • W • B             ≈⟨ front _ V-W ⟩
    ε • B • V • W • B                   ≈⟨ left-unit ⟩
    B • V • W • B                       ≈⟨ back _ (sym assoc) ⟩
    B • (V • W) • B                     ≈⟨ back _ (front _ V-W) ⟩
    B • ε • B                           ≈⟨ back _ left-unit ⟩
    B • B                               ≈⟨ B□² k complete ⟩
    ε ∎
