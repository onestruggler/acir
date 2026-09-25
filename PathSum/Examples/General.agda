------------------------------------------------------------------------
-- Presentations of groups
--
-- The general rules [ω] and [Case] at work
--
-- Examples 3.3, 3.4 and B.2 use the general [HH] and [Elim]
-- (PathSum.Examples.Toffoli, .ControlledT, .Adder).  The other two
-- general rules of figure 2 are exercised here, so that every smart
-- constructor of PathSum.Reduction.General.Decidable runs on a closed
-- instance.
--
--  * [ω] with a Boolean-valued quotient: example B.1's chain, on the
--    true (SH)³ of PathSum.Examples.AppendixB, with the lift
--    x + y2 - 2xy2 of x ⊕ y2 as [ω]'s quotient and x as [HH]'s.  The
--    general rules reach ω I exactly as the linear ones do there.
--  * [Case]: the paper applies it only inside the proof of a
--    two-qubit Clifford+T identity it does not print in full, so the
--    instance here is built for the purpose and is not the paper's:
--    ¼y1x + ½y1y2 + ¼y2(1 - x), output x, is both
--    ¼y1X + ½y1(y2 + Q) + R and ¼y2(1 - X) + ½y2(y1 + Q′) + R′ with
--    X = x and Q = Q′ = 0, and [Case] reduces it to the identity.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.General where

open import Data.Fin.Base using (zero)
open import Data.Integer.Base using (+_)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Reduction 3 using (elim-reduct)
open import PathSum.Reduction.General 3 using
  (ωᴳ-reduct; hhᴳ-reduct; case-reduct)
open import PathSum.Reduction.General.Decidable 3 using
  (ωᴳ!; hhᴳ!; elimᴳ!; caseᴳ!)
open import PathSum.Reduction.Derivation 0 using
  (Derivation; _⟶⟨_⟩_; _≈⟨⟩_; _∎; derivation-sound)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Examples.Base using
  (_⋆_; mono; ωI; x₁; y₁; y₂)
open import PathSum.Examples.AppendixB using (SH³ᵖ)


------------------------------------------------------------------------
-- [ω]: (SH)³ = ω I again

-- The quotient of [ω] at y1: x ⊕ y2, lifted (y2 is now the first path
-- variable).

Q-ω : Poly 1 2
Q-ω = mono x₁ +ᴾ mono y₁ -ᴾ (+ 2) ·ᴾ mono (x₁ ∪ᵐ y₁)

SH³ᴳ₁ : PathSum 1 2 2
SH³ᴳ₁ = ωᴳ-reduct SH³ᵖ Q-ω

-- [HH] at y2, y3 ← x.

SH³ᴳ₂ : PathSum 1 2 1
SH³ᴳ₂ = hhᴳ-reduct SH³ᴳ₁ zero (mono x₁)

SH³ᴳ₃ : PathSum 1 0 0
SH³ᴳ₃ = elim-reduct SH³ᴳ₂

SH³-derivationᴳ : Derivation SH³ᵖ ωI
SH³-derivationᴳ =
  SH³ᵖ  ⟶⟨ ωᴳ! SH³ᵖ Q-ω ⟩
  SH³ᴳ₁ ⟶⟨ hhᴳ! SH³ᴳ₁ zero (mono x₁) ⟩
  SH³ᴳ₂ ⟶⟨ elimᴳ! SH³ᴳ₂ ⟩
  SH³ᴳ₃ ≈⟨⟩
  ωI    ∎

SH³ᵖ-ωᴳ : SH³ᵖ ≋ ωI
SH³ᵖ-ωᴳ = derivation-sound SH³-derivationᴳ


------------------------------------------------------------------------
-- [Case]

-- ¼y1x + ½y1y2 + ¼y2 - ¼xy2, output x.

Caseᵖ : PathSum 1 2 2
Caseᵖ = ⟨ (+ 2) ⋆ (y₁ ∪ᵐ x₁) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 2) ⋆ y₂
          +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₂)
        , (λ _ → μ x[ zero ]) ⟩

-- X = x, Q = Q′ = 0.

Case₁ : PathSum 1 0 0
Case₁ = case-reduct Caseᵖ (mono x₁) 0ᴾ 0ᴾ

Case-derivation : Derivation Caseᵖ idPS
Case-derivation =
  Caseᵖ ⟶⟨ caseᴳ! Caseᵖ (mono x₁) 0ᴾ 0ᴾ ⟩
  Case₁ ≈⟨⟩
  idPS  ∎

Case-id : Caseᵖ ≋ idPS
Case-id = derivation-sound Case-derivation
