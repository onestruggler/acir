------------------------------------------------------------------------
-- Presentations of groups
--
-- Example 3.3: the Toffoli gate
--
-- The paper recalls that the standard Clifford+T implementation of the
-- Toffoli gate has the path-sum
--
--    |x1x2x3⟩ ↦ 1/√2² Σ_{y1,y2} e^{2πi ½(x3y1 + x1x2y1 + y1y2)}
--                 |x1x2y2⟩
--
-- and verifies that it is the functional specification
-- |x1x2x3⟩ ↦ |x1x2(x3 ⊕ x1x2)⟩ "with the following sequence of
-- reductions and algebraic manipulations":
--
--    ↦ 1/√2² Σ_{y1,y2} e^{2πi ½y1(y2 + x3 + x1x2)} |x1x2y2⟩
--    ↦ 1/√2² Σ_{y2} |x1x2(x3 ⊕ x1x2)⟩                         [HH]
--    ↦ |x1x2(x3 ⊕ x1x2)⟩                                      [Elim]
--
-- The [HH] step's quotient x3 ⊕ x1x2 is not Z₂-linear, so it is an
-- instance of the general rule (PathSum.Reduction.General), whose
-- quotient Q must be Boolean-valued: Q is the lift of x3 ⊕ x1x2,
-- x3 + x1x2 - 2x1x2x3, which agrees with the paper's x3 + x1x2 inside
-- ½·(…) modulo 1.  The derivation below is the paper's column line by
-- line (PathSum.Reduction.Derivation): each printed line is a literal,
-- each rule is applied with the paper's quotient and its premises
-- decided by computation, and the formal reduct of each rule is shown
-- to be the printed next line by a congruence, also computed.  So
-- Toffoliᵖ ≋ Toffoliˢ by the paper's own route (Toffoli-spec).  That
-- the quotient literal is the paper's lifted Boolean expression, in
-- the sense of section 2, is checked too (Q-Toffoli-lift).
--
-- The paper does not print the circuit.  ToffoliC is Nielsen and
-- Chuang's seven-T implementation over {H, CNOT, T, T†}
-- (PathSum.CRK.Circuit at M = 3).  Its path-sum is the paper's once its
-- two path variables are swapped (ToffoliC-literal: the circuit lists
-- the newest first), so the circuit implements the Toffoli gate
-- (ToffoliC-spec).  PathSum.Examples.Brute cross-checks the claim by
-- brute force.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Toffoli where

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
  (_⋆_; mono; x₁; x₂; x₃; y₁; y₂; module CRK;
   crk-renumbered-≋; crk-≋-trans)


------------------------------------------------------------------------
-- The paper's column

-- ½(x3y1 + x1x2y1 + y1y2), outputs x1 x2 y2.

Toffoliᵖ : PathSum 3 2 2
Toffoliᵖ = ⟨ (+ 4) ⋆ (x₃ ∪ᵐ y₁) +ᴾ (+ 4) ⋆ (x₁ ∪ᵐ x₂ ∪ᵐ y₁)
           +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ y₂)
           , outs ⟩
  where
  outs : Fin 3 → Poly 3 2
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc zero ]

-- ½y1(y2 + x3 + x1x2): y1 factored out.

Toffoli-line₂ : PathSum 3 2 2
Toffoli-line₂ = ⟨ (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₃)
                +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁ ∪ᵐ x₂)
                , outs ⟩
  where
  outs : Fin 3 → Poly 3 2
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ y[ suc zero ]

-- The quotient x3 ⊕ x1x2, lifted: x3 + x1x2 - 2x1x2x3, in the
-- variables that remain once y1 is gone (y2 is now the first).

Q-Toffoli : Poly 3 1
Q-Toffoli = mono x₃ +ᴾ mono (x₁ ∪ᵐ x₂) -ᴾ (+ 2) ·ᴾ mono (x₁ ∪ᵐ x₂ ∪ᵐ x₃)

x₃⊕x₁x₂ : BExp 3 1
x₃⊕x₁x₂ = var x[ suc (suc zero) ] ⊕ᵉ (var x[ zero ] ∧ᵉ var x[ suc zero ])

Q-Toffoli-lift : ∀ γ → Q-Toffoli γ ≡ liftᵉ x₃⊕x₁x₂ γ
Q-Toffoli-lift = liftOf⇒≡ x₃⊕x₁x₂ Q-Toffoli
  (toWitness {a? = liftOf? x₃⊕x₁x₂ Q-Toffoli} tt)

-- [HH] at y1, y2 ← x3 ⊕ x1x2.

Toffoli₁ : PathSum 3 2 1
Toffoli₁ = hhᴳ-reduct Toffoli-line₂ zero Q-Toffoli

-- 1/√2² Σ_{y2} |x1 x2 (x3 ⊕ x1x2)⟩: y2 is now a dummy variable.

Toffoli-line₃ : PathSum 3 2 1
Toffoli-line₃ = ⟨ 0ᴾ , outs ⟩
  where
  outs : Fin 3 → Poly 3 1
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ x[ suc (suc zero) ] +ᴾ mono (x₁ ∪ᵐ x₂)

-- [Elim] of y2.

Toffoli₂ : PathSum 3 0 0
Toffoli₂ = elim-reduct Toffoli-line₃

-- |x1 x2 (x3 ⊕ x1x2)⟩; outputs are read modulo 2.

Toffoliˢ : PathSum 3 0 0
Toffoliˢ = ⟨ 0ᴾ , outs ⟩
  where
  outs : Fin 3 → Poly 3 0
  outs zero             = μ x[ zero ]
  outs (suc zero)       = μ x[ suc zero ]
  outs (suc (suc zero)) = μ x[ suc (suc zero) ] +ᴾ mono (x₁ ∪ᵐ x₂)

Toffoli-derivation : Derivation Toffoliᵖ Toffoliˢ
Toffoli-derivation =
  Toffoliᵖ      ≈⟨⟩
  Toffoli-line₂ ⟶⟨ hhᴳ! Toffoli-line₂ zero Q-Toffoli ⟩
  Toffoli₁      ≈⟨⟩
  Toffoli-line₃ ⟶⟨ elimᴳ! Toffoli-line₃ ⟩
  Toffoli₂      ≈⟨⟩
  Toffoliˢ      ∎

Toffoli-spec : Toffoliᵖ ≋ Toffoliˢ
Toffoli-spec = derivation-sound Toffoli-derivation


------------------------------------------------------------------------
-- The circuit

-- Controls x1 and x2, target x3: a CCZ between two Hadamards on the
-- target, the CCZ being ⅛ of
--   x1 + x2 + y - (x1 ⊕ x2) - (x1 ⊕ y) - (x2 ⊕ y) + (x1 ⊕ x2 ⊕ y)
--   = 4x1x2y
-- (T = R 3, T† = R† 3).  The head of the list is applied first.

ToffoliC : CRK.Circuit 3
ToffoliC =
  H c ∷ CNOT b c (λ ()) ∷ R† 3 c ∷ CNOT a c (λ ()) ∷ R 3 c ∷
  CNOT b c (λ ()) ∷ R† 3 c ∷ CNOT a c (λ ()) ∷ R 3 c ∷ R 3 b ∷ H c ∷
  CNOT a b (λ ()) ∷ R† 3 b ∷ CNOT a b (λ ()) ∷ R 3 a ∷ []
  where
  open CRK using (H; CNOT; R; R†)

  a b c : Fin 3
  a = zero
  b = suc zero
  c = suc (suc zero)

-- The circuit lists y2 before y1; swapped, its path-sum is the
-- paper's.

ToffoliC-literal : CRK.⟦ ToffoliC ⟧ ≋ Toffoliᵖ
ToffoliC-literal =
  crk-renumbered-≋ ToffoliC Toffoliᵖ (suc zero ∷ []) refl refl

ToffoliC-spec : CRK.⟦ ToffoliC ⟧ ≋ Toffoliˢ
ToffoliC-spec =
  crk-≋-trans ToffoliC Toffoliᵖ Toffoliˢ ToffoliC-literal Toffoli-spec
