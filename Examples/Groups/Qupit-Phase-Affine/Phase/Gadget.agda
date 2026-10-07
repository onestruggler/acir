------------------------------------------------------------------------
-- Presentations of groups
--
-- Phase gadgets: a one-wire diagonal gate on the sum of two wires
--
-- Rule (7) factors CX through the swap (CX-factor):
--
--     CX = CXʳ • M₋₁↑ • SWAP • CXʳ
--
-- so a gate G on wire 0 that commutes with CXʳ (G on its control) and
-- with M₋₁ on wire 1, and that SWAP moves to G' on wire 1, slides
-- through it (gadget):
--
--     G • CX ≈ CX • CXʳ⁻¹ • G' • CXʳ
--
-- that is, G on x₀ + x₁ can be written with either wire as the
-- target: the paper's PhaseGadgetS and PhaseGadgetT, for Z, S, T and
-- their iterates at once.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Gadget
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; 1F ; -_ ; -1*)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (conjᶠ)

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    R R⁻ m : Circuit (₂₊ n)
    R  = CXʳ
    R⁻ = CXʳ ^ᶠ (- 1F)
    m  = M⟨ -1* ⟩ ↑

    module OR = Pow.Order (₂₊ n) {CXʳ} CXʳ-order

    RR⁻ : (₂₊ n) ⊢ R • R⁻ ≈ ε
    RR⁻ = OR.inverseʳ

    R⁻R : (₂₊ n) ⊢ R⁻ • R ≈ ε
    R⁻R = OR.inverseˡ

    mm : (₂₊ n) ⊢ m • m ≈ ε
    mm = lift (Width.trans (ax (ax2 -1* -1*)) (Width.trans (Width.refl' (₁₊ n) (M-≡ neg²)) (ax ax1)))
      where
      open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
        using (_*_ ; solve ; _:*_ ; :-_ ; _:=_ ; con)
      import Data.Integer.Base as ℤ
      neg² : - 1F * - 1F ≡ 1F
      neg² = solve 0 ((:- con (ℤ.+ 1)) :* (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl

  -- Rule (7), turned around.
  CX-factor : (₂₊ n) ⊢ CX ≈ R • m • SWAP • R
  CX-factor = begin
    CX                                   ≈⟨ sym (trans (cancel-in RR⁻ _) (cancel-at R⁻R _)) ⟩
    R • R⁻ • CX • R⁻ • R                 ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
    R • (R⁻ • CX • R⁻) • R               ≈⟨ back _ (front _ (sym mswap)) ⟩
    R • (m • SWAP) • R                   ≈⟨ back _ assoc ⟩
    R • m • SWAP • R                     ∎
    where
    -- SWAP = m R⁻ CX R⁻ (rule (7)), so m SWAP = R⁻ CX R⁻.
    mswap : (₂₊ n) ⊢ m • SWAP ≈ R⁻ • CX • R⁻
    mswap = begin
      m • SWAP                           ≈⟨ back _ (ax ax7) ⟩
      m • m • (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP • CX ^ᶠ (- 1F) • SWAP)
                                         ≈⟨ cancel-in mm _ ⟩
      (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP • CX ^ᶠ (- 1F) • SWAP)
                                         ≈⟨ cong (conjᶠ (ax swap-order) sCX (- 1F))
                                                 (back _ (conjᶠ (ax swap-order) sCX (- 1F))) ⟩
      R⁻ • CX • R⁻                       ∎

  -- A gate on wire 0 that commutes with CXʳ and with M₋₁ on wire 1,
  -- and that SWAP moves to G' on wire 1.
  gadget : {G G' : Circuit (₂₊ n)} →
           (₂₊ n) ⊢ G • R ≈ R • G → (₂₊ n) ⊢ G • m ≈ m • G → (₂₊ n) ⊢ G • SWAP ≈ SWAP • G' →
           (₂₊ n) ⊢ G • CX ≈ CX • R⁻ • G' • R
  gadget {G} {G'} GR Gm Gs = begin
    G • CX                               ≈⟨ back _ CX-factor ⟩
    G • R • m • SWAP • R                 ≈⟨ trans (sym assoc) (trans (front _ GR) assoc) ⟩
    R • G • m • SWAP • R                 ≈⟨ back _ (trans (sym assoc) (trans (front _ Gm) assoc)) ⟩
    R • m • G • SWAP • R                 ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ Gs) assoc))) ⟩
    R • m • SWAP • G' • R                ≈⟨ back _ (back _ (back _ (sym (cancel-in RR⁻ _)))) ⟩
    R • m • SWAP • R • R⁻ • G' • R       ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • □ • □ • □) • □ • □ • □) Eq.refl ⟩
    (R • m • SWAP • R) • R⁻ • G' • R     ≈⟨ front _ (sym CX-factor) ⟩
    CX • R⁻ • G' • R                     ∎
