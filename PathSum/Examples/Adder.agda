------------------------------------------------------------------------
-- Presentations of groups
--
-- Example B.2: the one-bit full adder
--
-- The paper gives the reversible specification of the one-bit full
-- adder,
--
--    |x1x2x3x4⟩ ↦ |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3)
--                  (x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4)⟩,
--
-- a Clifford+T implementation obtained by Reed-Muller decoding, and
-- the check
--
--    |x1x2x3x4⟩ ↦ 1/√2² Σ_{y1,y2} e^{2πi ½(y1y2 + y1x1x2 + y1x1x3
--                    + y1x2x3 + y1x4)} |x1 (x1⊕x2)(x1⊕x2⊕x3) y2⟩
--      ↦ 1/√2² Σ_{y1,y2} e^{2πi ½y1(y2 + x1x2 + x1x3 + x2x3 + x4)}
--                    |x1 (x1⊕x2)(x1⊕x2⊕x3) y2⟩
--      ↦ |x1 (x1⊕x2)(x1⊕x2⊕x3)(x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4)⟩    [HH, Elim]
--
-- The [HH] step solves y2 = x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4, a quotient that
-- is not Z₂-linear, so it is the general rule of
-- PathSum.Reduction.General, whose quotient is the Boolean-valued lift
-- (Q-Adder, checked to be the lift of the paper's expression in the
-- sense of section 2: Q-Adder-lift).  The derivation follows the
-- column (PathSum.Reduction.Derivation), every premise decided by
-- computation: Adder-spec.
--
-- The circuit, AdderC, is read off the paper's figure over
-- {H, CNOT, T, P}; P is the phase gate S (R 2 here), the notation of
-- the Reed-Muller paper the figure comes from -- and with P = S the
-- circuit's path-sum is the paper's first line, which is checked
-- (AdderC-literal, once the circuit's two path variables are swapped:
-- it lists the newest first).  So the circuit implements the adder
-- (AdderC-spec).  The statements about the circuit are made through
-- PathSum.Examples.Base's names (Implements C ζ is CRK.⟦ C ⟧ ≋ ζ),
-- which keeps their checking cheap.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Adder where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Polynomial.Boolean using
  (BExp; var; _⊕ᵉ_; _∧ᵉ_; liftᵉ)
open import PathSum.Polynomial.Decidable using (liftOf?; liftOf⇒≡)
open import PathSum.Reduction 3 using (elim-reduct)
open import PathSum.Reduction.General 3 using (hhᴳ-reduct)
open import PathSum.Reduction.General.Decidable 3 using (hhᴳ!; elimᴳ!)
open import PathSum.Reduction.Derivation 0 using
  (Derivation; _⟶⟨_⟩_; _≈⟨⟩_; _∎; derivation-sound)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Examples.Base using
  (_⋆_; mono; x₁; x₂; x₃; x₄; y₁; y₂; module CRK;
   Implements; crk-implements; crk-implements-trans)


------------------------------------------------------------------------
-- The paper's column

-- The outputs x1, x1 ⊕ x2, x1 ⊕ x2 ⊕ x3 (read modulo 2) and y2.

private
  outs : Fin 4 → Poly 4 2
  outs zero                   = μ x[ zero ]
  outs (suc zero)             = μ x[ zero ] +ᴾ μ x[ suc zero ]
  outs (suc (suc zero))       =
    μ x[ zero ] +ᴾ μ x[ suc zero ] +ᴾ μ x[ suc (suc zero) ]
  outs (suc (suc (suc zero))) = μ y[ suc zero ]

-- ½(y1y2 + y1x1x2 + y1x1x3 + y1x2x3 + y1x4).

Adderᵖ : PathSum 4 2 2
Adderᵖ = ⟨ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₂)
         +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₃) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₂ ∪ᵐ x₃)
         +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₄)
         , outs ⟩

-- ½y1(y2 + x1x2 + x1x3 + x2x3 + x4).

Adder-line₂ : PathSum 4 2 2
Adder-line₂ = ⟨ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₂)
              +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₃) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₂ ∪ᵐ x₃)
              +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₄)
              , outs ⟩

-- The quotient x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4, lifted: the majority
-- x1x2 + x1x3 + x2x3 - 2x1x2x3, exclusive-or x4.

Q-Adder : Poly 4 1
Q-Adder =
  mono (x₁ ∪ᵐ x₂) +ᴾ mono (x₁ ∪ᵐ x₃) +ᴾ mono (x₂ ∪ᵐ x₃)
  -ᴾ (+ 2) ·ᴾ mono (x₁ ∪ᵐ x₂ ∪ᵐ x₃) +ᴾ mono x₄
  -ᴾ (+ 2) ·ᴾ mono (x₁ ∪ᵐ x₂ ∪ᵐ x₄) -ᴾ (+ 2) ·ᴾ mono (x₁ ∪ᵐ x₃ ∪ᵐ x₄)
  -ᴾ (+ 2) ·ᴾ mono (x₂ ∪ᵐ x₃ ∪ᵐ x₄)
  +ᴾ (+ 4) ·ᴾ mono (x₁ ∪ᵐ x₂ ∪ᵐ x₃ ∪ᵐ x₄)

carry : BExp 4 1
carry = (var x[ zero ] ∧ᵉ var x[ suc zero ])
        ⊕ᵉ (var x[ zero ] ∧ᵉ var x[ suc (suc zero) ])
        ⊕ᵉ (var x[ suc zero ] ∧ᵉ var x[ suc (suc zero) ])
        ⊕ᵉ var x[ suc (suc (suc zero)) ]

Q-Adder-lift : ∀ γ → Q-Adder γ ≡ liftᵉ carry γ
Q-Adder-lift = liftOf⇒≡ carry Q-Adder
  (toWitness {a? = liftOf? carry Q-Adder} tt)

-- [HH] at y1, y2 ← the carry, then [Elim] of the dummy y2.

Adder₁ : PathSum 4 2 1
Adder₁ = hhᴳ-reduct Adder-line₂ zero Q-Adder

Adder₂ : PathSum 4 0 0
Adder₂ = elim-reduct Adder₁

-- |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3) (x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4)⟩.

Adderˢ : PathSum 4 0 0
Adderˢ = ⟨ 0ᴾ , outsˢ ⟩
  where
  outsˢ : Fin 4 → Poly 4 0
  outsˢ zero                   = μ x[ zero ]
  outsˢ (suc zero)             = μ x[ zero ] +ᴾ μ x[ suc zero ]
  outsˢ (suc (suc zero))       =
    μ x[ zero ] +ᴾ μ x[ suc zero ] +ᴾ μ x[ suc (suc zero) ]
  outsˢ (suc (suc (suc zero))) =
    mono (x₁ ∪ᵐ x₂) +ᴾ mono (x₁ ∪ᵐ x₃) +ᴾ mono (x₂ ∪ᵐ x₃) +ᴾ mono x₄

Adder-derivation : Derivation Adderᵖ Adderˢ
Adder-derivation =
  Adderᵖ      ≈⟨⟩
  Adder-line₂ ⟶⟨ hhᴳ! Adder-line₂ zero Q-Adder ⟩
  Adder₁      ⟶⟨ elimᴳ! Adder₁ ⟩
  Adder₂      ≈⟨⟩
  Adderˢ      ∎

Adder-spec : Adderᵖ ≋ Adderˢ
Adder-spec = derivation-sound Adder-derivation


------------------------------------------------------------------------
-- The circuit

-- The paper's figure, column by column (P = S = R 2, T = R 3); the
-- head of the list is applied first.

AdderC : CRK.Circuit 4
AdderC =
  H d ∷
  R 2 a ∷ R 2 b ∷ R 2 c ∷ R 2 d ∷
  CNOT a b (λ ()) ∷
  CNOT c a (λ ()) ∷
  R 3 a ∷ R 3 b ∷ R 3 d ∷
  CNOT a b (λ ()) ∷
  CNOT d a (λ ()) ∷
  CNOT b d (λ ()) ∷
  R 3 a ∷ R 3 b ∷ R 3 d ∷
  CNOT b a (λ ()) ∷
  R 3 a ∷
  CNOT c a (λ ()) ∷
  R 2 a ∷
  CNOT d a (λ ()) ∷
  CNOT b d (λ ()) ∷
  CNOT c b (λ ()) ∷
  CNOT a b (λ ()) ∷
  CNOT b c (λ ()) ∷
  H d ∷ []
  where
  open CRK using (H; CNOT; R)

  a b c d : Fin 4
  a = zero
  b = suc zero
  c = suc (suc zero)
  d = suc (suc (suc zero))

-- The circuit lists y2 before y1; swapped, its path-sum is the
-- paper's (Implements C ζ is CRK.⟦ C ⟧ ≋ ζ).

AdderC-literal : Implements AdderC Adderᵖ
AdderC-literal = crk-implements AdderC Adderᵖ (suc zero ∷ []) refl refl

AdderC-spec : Implements AdderC Adderˢ
AdderC-spec =
  crk-implements-trans AdderC Adderᵖ Adderˢ AdderC-literal Adder-spec
