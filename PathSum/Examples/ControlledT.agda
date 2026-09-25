------------------------------------------------------------------------
-- Presentations of groups
--
-- Example 3.4: controlled-T with an ancilla
--
-- The paper implements controlled-T, |x1x2⟩ ↦ e^{2πi x1x2/8}|x1x2⟩,
-- over Clifford+T with an ancilla prepared in |0⟩, computes the
-- canonical path-sum of the circuit and reduces it:
--
--    |x1x2⟩|0⟩
--      ↦ 1/√2⁴ Σ_y e^{2πi ⅛(4x1x2y1 + 4x1y2 + 4y1y2 + y2 + 4y2y3
--                  + 4x1x2y3 + 4x1y4 + 4y3y4 + 4x1x2)} |x1x2y4⟩
--      ↦ 1/√2⁴ Σ_y e^{2πi (½y1(y2 + x1x2) + ⅛(4x1y2 + y2 + 4y2y3
--                  + 4x1x2y3 + 4x1y4 + 4y3y4 + 4x1x2))} |x1x2y4⟩
--      ↦ 1/√2² Σ_{y3,y4} e^{2πi ⅛(4x1x2 + x1x2 + 4x1x2y3 + 4x1x2y3
--                  + 4x1y4 + 4y3y4 + 4x1x2)} |x1x2y4⟩     [HH, Elim]
--      ↦ 1/√2² Σ_{y3,y4} e^{2πi (½y3y4 + ⅛(x1y4 + x1x2))} |x1x2y4⟩
--      ↦ e^{2πi x1x2/8} |x1x2⟩|0⟩                       [HH, Elim]
--
-- concluding that "the above circuit implements the controlled-T gate,
-- and provably leaves the ancilla clean".
--
-- PathSum.Base has no constant inputs, so the ancilla is a third input
-- x3.  The path-sum above does not mention it; as a path-sum on three
-- qubits (cTᵖ) it is the circuit on the inputs where x3 = 0, and its
-- specification (cTˢ) is |x1x2x3⟩ ↦ e^{2πi x1x2/8}|x1x2 0⟩ -- neither
-- is unitary on three qubits, controlled-T being the part at x3 = 0.
-- The derivation follows the paper's column (the first [HH] solves
-- y2 = x1x2, a quotient that is not Z₂-linear, so it is the general
-- rule of PathSum.Reduction.General; the second solves y4 = 0), with
-- one correction.  The fourth line is misprinted: from the third,
-- ⅛(9x1x2 + 8x1x2y3 + 4x1y4 + 4y3y4) is ½y3y4 + ½x1y4 + ⅛x1x2 modulo
-- 1, not ½y3y4 + ⅛(x1y4 + x1x2) as printed.  The derivation uses the
-- corrected line (cT-line₄); the printed one is not the same path-sum
-- (cT-line₄-typo), but it reduces to the same end by the same last step
-- (cT-line₄ᵖ-≋), since [HH] sets y4 to 0 and the misprinted term with
-- it, so the conclusion stands.  cT-spec : cTᵖ ≋ cTˢ.
--
-- The circuit itself, cTC, is read off the paper's figure, over
-- {H, CNOT, T, T†, S, S†} (PathSum.CRK.Circuit at M = 3, S = R 2), with
-- the ancilla as its third qubit.  Its path-sum with x3 set to 0
-- (PathSum.Ancilla.set0) is the paper's first line once its path
-- variables are renumbered (cTC-literal: the circuit lists the newest
-- first), so, on the inputs whose ancilla is |0⟩, the circuit is
-- controlled-T on the first two qubits with the ancilla returned in
-- |0⟩ (cTC-spec, an equivalence of the columns at those inputs), and
-- every amplitude to an output whose ancilla is 1 vanishes
-- (cTC-clean): the paper's two claims.  These three are stated through
-- PathSum.Examples.Base's names Literal₀, Implements₀ and Clean₀, which
-- unfold (by refl) to set0 ancilla CRK.⟦ cTC ⟧ ≋ cTᵖ, to
-- CRK.⟦ cTC ⟧ ≋[ ancilla ]₀ cTˢ and to the vanishing of those
-- amplitudes.  Written out, the first was still being matched against
-- the lemma that proves it when stopped after ten minutes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.ControlledT where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (suc)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Reduction 3 using (elim-reduct)
open import PathSum.Reduction.General 3 using (hhᴳ-reduct)
open import PathSum.Reduction.General.Decidable 3 using (hhᴳ!; elimᴳ!)
open import PathSum.Reduction.Derivation 0 using
  (Derivation; _⟶⟨_⟩_; _≈⟨⟩_; _∎; derivation-sound)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Congruence 0 using (Congruent; congruent?)
open import PathSum.Examples.Base using
  (yᵐ; _⋆_; mono; x₁; x₂; y₁; y₂; y₃; y₄; module CRK;
   Literal₀; Implements₀; Clean₀; crk-literal₀; crk-implements₀;
   crk-clean₀)

private
  -- Once y1 and y2 are gone, the paper's y3 and y4 are the first and
  -- second path variables.

  y₃′ : ∀ {n m} → Mon n (suc m)
  y₃′ = yᵐ zero

  y₄′ : ∀ {n m} → Mon n (suc (suc m))
  y₄′ = yᵐ (suc zero)


------------------------------------------------------------------------
-- The paper's column

-- ⅛(4x1x2y1 + 4x1y2 + 4y1y2 + y2 + 4y2y3 + 4x1x2y3 + 4x1y4 + 4y3y4
-- + 4x1x2), outputs x1 x2 y4; the third input, the ancilla, does not
-- occur.

cTᵖ : PathSum 3 4 4
cTᵖ = ⟨ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₁) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₂)
      +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 1) ⋆ y₂ +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃)
      +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₄)
      +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂)
      , outs ⟩
  where
  outs : Fin 3 → Poly 3 4
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc (suc (suc zero)) ]

-- ½y1(y2 + x1x2) + ⅛(4x1y2 + y2 + 4y2y3 + 4x1x2y3 + 4x1y4 + 4y3y4
-- + 4x1x2).

cT-line₂ : PathSum 3 4 4
cT-line₂ = ⟨ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₂)
           +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₂) +ᴾ (+ 1) ⋆ y₂ +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃)
           +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₄)
           +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂)
           , outs ⟩
  where
  outs : Fin 3 → Poly 3 4
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc (suc (suc zero)) ]

-- [HH] at y1, y2 ← x1x2 (a product of bits, its own lift), then
-- [Elim] of the dummy y2.

Q-cT : Poly 3 3
Q-cT = mono (x₁ ∪ᵐ x₂)

cT₁ : PathSum 3 4 3
cT₁ = hhᴳ-reduct cT-line₂ zero Q-cT

cT₂ : PathSum 3 2 2
cT₂ = elim-reduct cT₁

-- ⅛(4x1x2 + x1x2 + 4x1x2y3 + 4x1x2y3 + 4x1y4 + 4y3y4 + 4x1x2), as
-- printed, outputs x1 x2 y4.

cT-line₃ : PathSum 3 2 2
cT-line₃ = ⟨ (+ 4) ⋆ (x₁ ∪ᵐ x₂) +ᴾ (+ 1) ⋆ (x₁ ∪ᵐ x₂)
           +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₃′) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₃′)
           +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₄′) +ᴾ (+ 4) ⋆ (y₃′ ∪ᵐ y₄′)
           +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂)
           , outs ⟩
  where
  outs : Fin 3 → Poly 3 2
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc zero ]

-- ½y3y4 + ½x1y4 + ⅛x1x2: the fourth line, corrected.

cT-line₄ : PathSum 3 2 2
cT-line₄ = ⟨ (+ 4) ⋆ (y₃′ ∪ᵐ y₄′) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ y₄′)
           +ᴾ (+ 1) ⋆ (x₁ ∪ᵐ x₂)
           , outs ⟩
  where
  outs : Fin 3 → Poly 3 2
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc zero ]

-- [HH] at y3, y4 ← 0, then [Elim] of the dummy y4.

cT₃ : PathSum 3 2 1
cT₃ = hhᴳ-reduct cT-line₄ zero 0ᴾ

cT₄ : PathSum 3 0 0
cT₄ = elim-reduct cT₃

-- |x1 x2 x3⟩ ↦ e^{2πi x1x2/8} |x1 x2 0⟩.

cTˢ : PathSum 3 0 0
cTˢ = ⟨ (+ 1) ⋆ (x₁ ∪ᵐ x₂) , outs ⟩
  where
  outs : Fin 3 → Poly 3 0
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = 0ᴾ

cT-derivation : Derivation cTᵖ cTˢ
cT-derivation =
  cTᵖ      ≈⟨⟩
  cT-line₂ ⟶⟨ hhᴳ! cT-line₂ zero Q-cT ⟩
  cT₁      ⟶⟨ elimᴳ! cT₁ ⟩
  cT₂      ≈⟨⟩
  cT-line₃ ≈⟨⟩
  cT-line₄ ⟶⟨ hhᴳ! cT-line₄ zero 0ᴾ ⟩
  cT₃      ⟶⟨ elimᴳ! cT₃ ⟩
  cT₄      ≈⟨⟩
  cTˢ      ∎

cT-spec : cTᵖ ≋ cTˢ
cT-spec = derivation-sound cT-derivation


------------------------------------------------------------------------
-- The misprinted fourth line

-- ½y3y4 + ⅛(x1y4 + x1x2), as printed.

cT-line₄ᵖ : PathSum 3 2 2
cT-line₄ᵖ = ⟨ (+ 4) ⋆ (y₃′ ∪ᵐ y₄′) +ᴾ (+ 1) ⋆ (x₁ ∪ᵐ y₄′)
            +ᴾ (+ 1) ⋆ (x₁ ∪ᵐ x₂)
            , outs ⟩
  where
  outs : Fin 3 → Poly 3 2
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc zero ]

-- It is not the third line rewritten ...

cT-line₄-typo : ¬ Congruent cT-line₃ cT-line₄ᵖ
cT-line₄-typo = toWitnessFalse {a? = congruent? cT-line₃ cT-line₄ᵖ} tt

-- ... but the last step takes it to the same end.

cT₃ᵖ : PathSum 3 2 1
cT₃ᵖ = hhᴳ-reduct cT-line₄ᵖ zero 0ᴾ

cT₄ᵖ : PathSum 3 0 0
cT₄ᵖ = elim-reduct cT₃ᵖ

cT-line₄ᵖ-≋ : cT-line₄ᵖ ≋ cTˢ
cT-line₄ᵖ-≋ = derivation-sound
  (cT-line₄ᵖ ⟶⟨ hhᴳ! cT-line₄ᵖ zero 0ᴾ ⟩
   cT₃ᵖ      ⟶⟨ elimᴳ! cT₃ᵖ ⟩
   cT₄ᵖ      ≈⟨⟩
   cTˢ       ∎)


------------------------------------------------------------------------
-- The circuit

-- The paper's figure, column by column (a, b = x1, x2; c the
-- ancilla); the head of the list is applied first.

cTC : CRK.Circuit 3
cTC =
  CNOT a b (λ ()) ∷ H c ∷
  R† 2 a ∷ CNOT b c (λ ()) ∷
  CNOT c a (λ ()) ∷
  R 3 a ∷ R† 3 c ∷
  CNOT b a (λ ()) ∷
  CNOT b c (λ ()) ∷
  R 3 a ∷ R† 3 c ∷
  CNOT a c (λ ()) ∷
  H a ∷ R 3 a ∷ H a ∷
  CNOT a c (λ ()) ∷
  R† 3 a ∷ R 3 c ∷
  CNOT b c (λ ()) ∷
  CNOT b a (λ ()) ∷ R 3 c ∷
  R† 3 a ∷
  CNOT c a (λ ()) ∷
  R 2 a ∷ CNOT b c (λ ()) ∷
  CNOT a b (λ ()) ∷ H c ∷ []
  where
  open CRK using (H; CNOT; R; R†)

  a b c : Fin 3
  a = zero
  b = suc zero
  c = suc (suc zero)

-- The ancilla, the third qubit.

ancilla : Fin 3
ancilla = suc (suc zero)

-- With the ancilla set to 0 and its path variables in the order the
-- Hadamards introduce them, the circuit's path-sum is the paper's
-- first line: Literal₀ cTC ancilla cTᵖ is
-- set0 ancilla CRK.⟦ cTC ⟧ ≋ cTᵖ (PathSum.Examples.Base).

cTC-literal : Literal₀ cTC ancilla cTᵖ
cTC-literal = crk-literal₀ cTC ancilla cTᵖ
  (suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []) refl refl

-- On the inputs whose ancilla is |0⟩ the circuit is controlled-T,
-- returning the ancilla in |0⟩: CRK.⟦ cTC ⟧ ≋[ ancilla ]₀ cTˢ ...

cTC-spec : Implements₀ cTC ancilla cTˢ
cTC-spec = crk-implements₀ cTC ancilla cTᵖ cTˢ cTC-literal cT-spec

-- ... and no amplitude from such an input reaches an output whose
-- ancilla is 1.

cTC-clean : Clean₀ cTC ancilla
cTC-clean = crk-clean₀ cTC ancilla cTˢ cTC-spec (λ x y → eval-0ᴾ x y)
