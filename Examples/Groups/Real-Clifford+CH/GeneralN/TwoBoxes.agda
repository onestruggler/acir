------------------------------------------------------------------------
-- Presentations of groups
--
-- Two boxes with complementary controls commute, and the box passes the
-- triply controlled ZX (Clément, Lemma D.8, Equations (288)–(291))
--
-- At width 5 + k.  (288): the box A on wire 0 controlled by the wires
-- 1 2 3, and the box B on wire 2 controlled by wire 0 and the wires 4 …,
-- commute; (289): the same with B also controlled by wire 3.  Between
-- them their box wires and controls cover every wire, so there is no
-- idle wire to take the step one width down, and there can be none: a
-- box is odd on its support (its determinant there is −1) while every
-- circuit of three or more wires is even, so it needs its box wire.
-- The paper's proofs, rearranged as word algebra (`commute`): A is the
-- commutator of the doubly controlled ZX x from the wires 2 3 onto
-- wire 0 with the CZ c of the wires 0 1, (172); one width down, with
-- wire 1 idle, x and B generate the box B₀ on wire 0 controlled by the
-- wires 2 … — (269) there for (288), definitional under place 1, and a
-- semantic step for (289); c passes B and B₀.  Then
--
--     A B = x′ c x c B = x′ c x B c = x′ c B₀ B x c = x′ B₀ B c x c
--         = x′ x B x′ c x c = B A,
--
-- with x B = B₀ B x and B₀ B = x B x′, both from x B x′ B = B₀ and
-- B B = ε.
--
-- (290) and (291): the box on wire 2 controlled by the wire 1 and the
-- wires 4 … (for (291) also by wire 3), which is B□ k resp. B₁₀ (1 + k)
-- one wire up, passes the triply controlled ZX on wire 0,
-- ZX₃ = CH • B′ • CH • B′ with B′ the box on wire 1 controlled by the
-- wires 0 2 3: it passes the CH one width down, and B′ is (288) resp.
-- (289) under the swap of the wires 0 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.TwoBoxes
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (eq118 ; module S↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (CCZX₂₃ ; CCXZ₂₃ ; eq172)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq271 ; eq272)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemKey using (sem-box-CH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemBoxes
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (idle-comm ; place-yB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; box274)

-- At width 5 + k, with wire 1 idle: the box on wire 2 controlled by
-- wire 0 and the wires 4 … (wire 3 idle too), the same also controlled
-- by wire 3, and the box on wire 0 controlled by the wires 2 ….
B₂ B₃ B₀ : ∀ k → Circuit (₁₊ (₄₊ k))
B₂ k = place 1 (B□ k)
B₃ k = place 1 (B₁₀ (₁₊ k))
B₀ k = place 1 (Λ□ (₃₊ k))

Eq288 Eq289 Eq290 Eq291 : ℕ → Set
Eq288 k = (₁₊ (₄₊ k)) ⊢ (Λ□ 3 ↓ᵏ (₁₊ k)) • B₂ k ≈ B₂ k • (Λ□ 3 ↓ᵏ (₁₊ k))
Eq289 k = (₁₊ (₄₊ k)) ⊢ (Λ□ 3 ↓ᵏ (₁₊ k)) • B₃ k ≈ B₃ k • (Λ□ 3 ↓ᵏ (₁₊ k))
Eq290 k = (₁₊ (₄₊ k)) ⊢ B□ k ↑ • (ΛZX 3 ↓ᵏ (₁₊ k)) ≈ (ΛZX 3 ↓ᵏ (₁₊ k)) • B□ k ↑
Eq291 k = (₁₊ (₄₊ k)) ⊢ B₁₀ (₁₊ k) ↑ • (ΛZX 3 ↓ᵏ (₁₊ k)) ≈ (ΛZX 3 ↓ᵏ (₁₊ k)) • B₁₀ (₁₊ k) ↑

module _ (k : ℕ) (complete : Complete (₁₊ k)) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)

    A x x′ c : Circuit (₁₊ (₄₊ k))
    A  = Λ□ 3 ↓ᵏ (₁₊ k)
    x  = CCZX₂₃
    x′ = CCXZ₂₃
    c  = CZ ↓

    ------------------------------------------------------------------
    -- What the two boxes A have in common

    x′x : (₁₊ (₄₊ k)) ⊢ x′ • x ≈ ε
    x′x = begin
      (Ex ↓ • (CCXZ ↓ᵏ (₁₊ k)) ↑ • Ex ↓) • (Ex ↓ • (CCZX ↓ᵏ (₁₊ k)) ↑ • Ex ↓)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      Ex ↓ • (CCXZ ↓ᵏ (₁₊ k)) ↑ • (Ex ↓ • Ex ↓) • (CCZX ↓ᵏ (₁₊ k)) ↑ • Ex ↓
        ≈⟨ back _ (back _ (trans (front _ Ex²) left-unit)) ⟩
      Ex ↓ • (CCXZ ↓ᵏ (₁₊ k)) ↑ • (CCZX ↓ᵏ (₁₊ k)) ↑ • Ex ↓
        ≈⟨ back _ (trans (sym assoc) (trans (front _ (lemma-cong↑ (CCXZ • CCZX) ε eq118)) left-unit)) ⟩
      Ex ↓ • Ex ↓
        ≈⟨ Ex² ⟩
      ε ∎

    -- (172): A is the commutator of x and c.
    A-form : (₁₊ (₄₊ k)) ⊢ x′ • c • x • c ≈ A
    A-form = begin
      x′ • c • x • c          ≈⟨ back _ (sym assoc) ⟩
      x′ • (c • x) • c        ≈⟨ back _ (front _ eq172) ⟩
      x′ • (x • A • c) • c    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x′ • x) • A • (c • c)  ≈⟨ cong x′x (back _ CZ²) ⟩
      ε • A • ε               ≈⟨ trans left-unit right-unit ⟩
      A ∎

    -- place 1 with its cycles written out.
    unit₁ : ∀ (u : Circuit (₄₊ k)) → (₁₊ (₄₊ k)) ⊢ place 1 u ≈ Ex ↓ • u ↑ • Ex ↓
    unit₁ u = cong left-unit (back _ right-unit)

    -- c passes the cycles of place 1, hence anything placed there whose
    -- lift it passes.
    c-cyc⁻¹ : (₁₊ (₄₊ k)) ⊢ c • cyc⁻¹ 1 ≈ cyc⁻¹ 1 • c
    c-cyc⁻¹ = L-sem (CZ • (ε • Ex)) ((ε • Ex) • CZ) Eq.refl

    c-cyc : (₁₊ (₄₊ k)) ⊢ c • cyc 1 ≈ cyc 1 • c
    c-cyc = L-sem (CZ • (Ex • ε)) ((Ex • ε) • CZ) Eq.refl

    c-place : ∀ {w : Circuit (₄₊ k)} → (₁₊ (₄₊ k)) ⊢ c • w ↑ ≈ w ↑ • c →
              (₁₊ (₄₊ k)) ⊢ c • place 1 w ≈ place 1 w • c
    c-place {w} e = begin
      c • cyc⁻¹ 1 • w ↑ • cyc 1     ≈⟨ sym assoc ⟩
      (c • cyc⁻¹ 1) • w ↑ • cyc 1   ≈⟨ front _ c-cyc⁻¹ ⟩
      (cyc⁻¹ 1 • c) • w ↑ • cyc 1   ≈⟨ assoc ⟩
      cyc⁻¹ 1 • c • w ↑ • cyc 1     ≈⟨ back _ (sym assoc) ⟩
      cyc⁻¹ 1 • (c • w ↑) • cyc 1   ≈⟨ back _ (front _ e) ⟩
      cyc⁻¹ 1 • (w ↑ • c) • cyc 1   ≈⟨ back _ (trans assoc (back _ c-cyc)) ⟩
      cyc⁻¹ 1 • w ↑ • cyc 1 • c     ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (cyc⁻¹ 1 • w ↑ • cyc 1) • c ∎

    c-B₀ : (₁₊ (₄₊ k)) ⊢ c • B₀ k ≈ B₀ k • c
    c-B₀ = c-place (eq272 k)

    -- A box placed with wire 1 idle that squares to ε is ε squared.
    place-invol : ∀ {w : Circuit (₄₊ k)} → ⟦ w • w ⟧ ~ ⟦ ε ⟧ →
                  (₁₊ (₄₊ k)) ⊢ place 1 w • place 1 w ≈ ε
    place-invol {w} e = begin
      place 1 w • place 1 w   ≈⟨ sym (place-• 1 w w) ⟩
      place 1 (w • w)         ≈⟨ lemma-5-1 1 complete e ⟩
      place 1 ε               ≈⟨ trans (back _ left-unit) (cyc⁻¹-cyc 1) ⟩
      ε ∎

    -- The four placed factors of (269), one width down.
    place-form : ∀ (w : Circuit (₄₊ k)) →
                 (₁₊ (₄₊ k)) ⊢ x • place 1 w • x′ • place 1 w ≈ place 1 (CCZX • w • CCXZ • w)
    place-form w = begin
      x • place 1 w • x′ • place 1 w
        ≈⟨ cong (sym (unit₁ CCZX)) (back _ (front _ (sym (unit₁ CCXZ)))) ⟩
      place 1 CCZX • place 1 w • place 1 CCXZ • place 1 w
        ≈⟨ sym (trans (place-• 1 CCZX (w • CCXZ • w)) (back _ (trans (place-• 1 w (CCXZ • w)) (back _ (place-• 1 CCXZ w))))) ⟩
      place 1 (CCZX • w • CCXZ • w) ∎

    ------------------------------------------------------------------
    -- The argument, for any B that squares to ε, generates B₀ with x as
    -- in (269), and passes c

    commute : ∀ {B} → (₁₊ (₄₊ k)) ⊢ B • B ≈ ε → (₁₊ (₄₊ k)) ⊢ x • B • x′ • B ≈ B₀ k →
              (₁₊ (₄₊ k)) ⊢ c • B ≈ B • c → (₁₊ (₄₊ k)) ⊢ A • B ≈ B • A
    commute {B} BB B₀-form c-B = begin
      A • B                           ≈⟨ front _ (sym A-form) ⟩
      (x′ • c • x • c) • B            ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      x′ • c • x • (c • B)            ≈⟨ back _ (back _ (back _ c-B)) ⟩
      x′ • c • x • (B • c)            ≈⟨ back _ (back _ (trans (sym assoc) (front _ xB))) ⟩
      x′ • c • (B₀ k • B • x) • c     ≈⟨ by-passoc (□ • □ • (□ • □ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
      x′ • (c • B₀ k) • B • x • c     ≈⟨ back _ (front _ c-B₀) ⟩
      x′ • (B₀ k • c) • B • x • c     ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      x′ • B₀ k • (c • B) • x • c     ≈⟨ back _ (back _ (front _ c-B)) ⟩
      x′ • B₀ k • (B • c) • x • c     ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
      x′ • (B₀ k • B) • c • x • c     ≈⟨ back _ (front _ B₀B) ⟩
      x′ • (x • B • x′) • c • x • c   ≈⟨ by-passoc (□ • (□ • □ • □) • □ • □ • □) ((□ • □) • □ • (□ • □ • □ • □)) Eq.refl ⟩
      (x′ • x) • B • (x′ • c • x • c) ≈⟨ cong x′x (back _ A-form) ⟩
      ε • B • A                       ≈⟨ left-unit ⟩
      B • A ∎
      where
      B₀B : (₁₊ (₄₊ k)) ⊢ B₀ k • B ≈ x • B • x′
      B₀B = begin
        B₀ k • B                  ≈⟨ front _ (sym B₀-form) ⟩
        (x • B • x′ • B) • B      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
        x • B • x′ • (B • B)      ≈⟨ back _ (back _ (back _ BB)) ⟩
        x • B • x′ • ε            ≈⟨ back _ (back _ right-unit) ⟩
        x • B • x′ ∎

      xB : (₁₊ (₄₊ k)) ⊢ x • B ≈ B₀ k • B • x
      xB = begin
        x • B                     ≈⟨ sym right-unit ⟩
        (x • B) • ε               ≈⟨ back _ (sym x′x) ⟩
        (x • B) • (x′ • x)        ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
        (x • B • x′) • x          ≈⟨ front _ (sym B₀B) ⟩
        (B₀ k • B) • x            ≈⟨ assoc ⟩
        B₀ k • B • x ∎

    ------------------------------------------------------------------
    -- c passes B one wire up (one width down, wire 3 idle) and B₁₀ one
    -- wire up ((271) under the swap of the wires 1 2)

    c-B□↑ : (₁₊ (₄₊ k)) ⊢ c • B□ k ↑ ≈ B□ k ↑ • c
    c-B□↑ = idle-comm 3 complete (place-low 3 CZ) (place-yB k) (sem-yB-CZ k)

    Ex-CZ₂₀ : (₁₊ (₄₊ k)) ⊢ S↑.⟪ CZ₂₀ ⟫ ≈ c
    Ex-CZ₂₀ = L₃-sem (Ex ↑ • CZ₂₀ • Ex ↑) CZ Eq.refl

    c-B₁₀↑ : (₁₊ (₄₊ k)) ⊢ c • B₁₀ (₁₊ k) ↑ ≈ B₁₀ (₁₊ k) ↑ • c
    c-B₁₀↑ = S↑.⟪⟫-≈ (eq271 k) (S↑.⟪⟫-•₂ Ex-CZ₂₀ refl) (S↑.⟪⟫-•₂ refl Ex-CZ₂₀)

  ----------------------------------------------------------------------
  -- (288) and (289)

  eq288 : Eq288 k
  eq288 = commute (place-invol (sem-B□² k)) (place-form (B□ k)) (c-place c-B□↑)

  eq289 : Eq289 k
  eq289 = commute (place-invol (sem-B₁₀² k))
                  (trans (place-form (B₁₀ (₁₊ k))) (lemma-5-1 1 complete (sem-B₁₀-form k)))
                  (c-place c-B₁₀↑)

  ----------------------------------------------------------------------
  -- (290) and (291)

  private
    module X = Conj {₁₊ (₄₊ k)} (Ex ↓) Ex²

    -- The box on wire 1 controlled by the wires 0 2 3, a factor of ZX₃.
    B′ : Circuit (₁₊ (₄₊ k))
    B′ = X.⟪ A ⟫

    unwrap : ∀ (w : Circuit (₄₊ k)) → (₁₊ (₄₊ k)) ⊢ X.⟪ place 1 w ⟫ ≈ w ↑
    unwrap w = begin
      Ex ↓ • place 1 w • Ex ↓             ≈⟨ back _ (front _ (unit₁ w)) ⟩
      Ex ↓ • (Ex ↓ • w ↑ • Ex ↓) • Ex ↓   ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex ↓ • Ex ↓) • w ↑ • (Ex ↓ • Ex ↓) ≈⟨ cong Ex² (back _ Ex²) ⟩
      ε • w ↑ • ε                         ≈⟨ trans left-unit right-unit ⟩
      w ↑ ∎

    -- A box commuting with A, carried by the swap of the wires 0 1.
    via-A : ∀ {w : Circuit (₄₊ k)} → (₁₊ (₄₊ k)) ⊢ A • place 1 w ≈ place 1 w • A →
            (₁₊ (₄₊ k)) ⊢ w ↑ • B′ ≈ B′ • w ↑
    via-A {w} e = X.⟪⟫-≈ (sym e) (X.⟪⟫-•₂ (unwrap w) refl) (X.⟪⟫-•₂ refl (unwrap w))

    pass• : ∀ {C a w : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ C • a ≈ a • C →
            (₁₊ (₄₊ k)) ⊢ C • w ≈ w • C → (₁₊ (₄₊ k)) ⊢ C • (a • w) ≈ (a • w) • C
    pass• {C} {a} {w} ea ew = begin
      C • (a • w)     ≈⟨ sym assoc ⟩
      (C • a) • w     ≈⟨ front _ ea ⟩
      (a • C) • w     ≈⟨ assoc ⟩
      a • (C • w)     ≈⟨ back _ ew ⟩
      a • (w • C)     ≈⟨ sym assoc ⟩
      (a • w) • C ∎

    -- ZX₃ is CH • B′ • CH • B′.
    pass-ZX₃ : ∀ {C : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ C • CH ↓ ≈ CH ↓ • C →
               (₁₊ (₄₊ k)) ⊢ C • B′ ≈ B′ • C →
               (₁₊ (₄₊ k)) ⊢ C • (CH ↓ • B′ • CH ↓ • B′) ≈ (CH ↓ • B′ • CH ↓ • B′) • C
    pass-ZX₃ eh eb = pass• eh (pass• eb (pass• eh eb))

    -- The CH passes B□ k one wire up: one width down, with wire 3 idle.
    B□↑-CH : (₁₊ (₄₊ k)) ⊢ B□ k ↑ • CH ↓ ≈ CH ↓ • B□ k ↑
    B□↑-CH = sym (idle-comm 3 complete (place-low 3 CH) (place-yB k) (sem-yB-CH k))

  -- B₁₀ one wire up is the box on wire 0 with wire 2 idle, (274); the
  -- CH passes that one width down.
  B₁₀↑-place : (₁₊ (₄₊ k)) ⊢ B₁₀ (₁₊ k) ↑ ≈ place 2 (Λ□ (₃₊ k))
  B₁₀↑-place = begin
      Ex ↑ • Λ□ (₃₊ k) ↑ • Ex ↑
        ≈⟨ back _ (front _ (sym (box274 (₁₊ k) complete))) ⟩
      Ex ↑ • (Ex ↓ • Λ□ (₃₊ k) ↑ • Ex ↓) • Ex ↑
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex ↑ • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • Ex ↑)
        ≈⟨ sym (cong (front _ left-unit) (back _ (back _ right-unit))) ⟩
      ((ε • Ex ↑) • Ex ↓) • Λ□ (₃₊ k) ↑ • (Ex ↓ • (Ex ↑ • ε)) ∎
    where open Tools ((₁₊ (₄₊ k)) VRel,_===_)

  private
    B₁₀↑-CH : (₁₊ (₄₊ k)) ⊢ B₁₀ (₁₊ k) ↑ • CH ↓ ≈ CH ↓ • B₁₀ (₁₊ k) ↑
    B₁₀↑-CH = begin
      B₁₀ (₁₊ k) ↑ • CH ↓               ≈⟨ front _ B₁₀↑-place ⟩
      place 2 (Λ□ (₃₊ k)) • CH ↓        ≈⟨ idle-comm 2 complete refl (place-low 2 CH) (sem-box-CH (₁₊ k)) ⟩
      CH ↓ • place 2 (Λ□ (₃₊ k))        ≈⟨ back _ (sym B₁₀↑-place) ⟩
      CH ↓ • B₁₀ (₁₊ k) ↑ ∎

  eq290 : Eq290 k
  eq290 = pass-ZX₃ B□↑-CH (via-A eq288)

  eq291 : Eq291 k
  eq291 = pass-ZX₃ B₁₀↑-CH (via-A eq289)
