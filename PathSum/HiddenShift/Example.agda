------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules simulate the hidden shift algorithm: one instance
--
-- PathSum.HiddenShift.Simulation proves, for every m, g and s, that a
-- reduction of the hidden shift circuit on |0⟩ which eliminates every
-- path variable ends at the path-sum |x⟩ ↦ |s⟩.  That such a reduction
-- exists is shown here for one instance, at M₀ = 0 (phases in eighths,
-- ½ = 4): m = 1 (n = 2 qubits), g(a) = a and s = (1, 0).
--
-- The derivation is the paper's: a column of lines, each obtained from
-- the one before by a rule of figure 2 (checked by computing its
-- premises, PathSum.Reduction.General.Decidable) or by rewriting the
-- polynomials modulo 1 and 2 (checked by computing the congruence).
-- Its first line is the circuit on |0⟩ itself, at0 (HS g₁ s₁), whose
-- polynomials are composites (PathSum.Compose) and do not compute; the
-- step to the written-out path-sum
--
--    Ξ₁ = ½(1 + a + b + ab + ac + bd + d + cd + ce + dh),  outputs e h,
--
-- (a b the first Hadamard layer's path, c d the second's, e h the
-- third's) is PathSum.HiddenShift.Simulation.at0-HS-congruent, whose
-- premises -- the outputs are the third layer's path, and the phase is
-- ½ hs-parity modulo 1 -- are checked at all 2^8 points.  Then
-- [HH] at a with b ← 1 - c, [Elim] of b, [HH] at c with e ← 1, [HH] at
-- d with h ← 0, and [Elim] of e and h reach |x⟩ ↦ |1 0⟩ with no path
-- variable and no normalisation left.  Every rule acts at the first
-- path variable.
--
-- By Simulation.hidden-shift-derives, any other complete derivation
-- would have ended at the same path-sum.  The search for a reduction
-- (PathSum.Full.Match.normal-formᶠ, which tries every rule at every
-- variable) is not run here; the chain is given.
--
-- The instances at M₀ = 0 of the modules the statements are made with
-- are re-exported, so that a restatement elsewhere uses the same
-- copies: two copies of a parameterised module's definitions are
-- matched only by unfolding both.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Example where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (1ℤ; +_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Congruence 0 using (Congruent)
open import PathSum.Denotation 0 public using
  (Assign; _≋_; outBit; outBit-μ)
open import PathSum.Examples.Base using (_⋆_)
open import PathSum.HiddenShift 0 public using (HS; specᴾ)
open import PathSum.HiddenShift.Simulation 0 public using
  (at0; layer₃; hs-parity; hs-parity-resp; at0-HS-congruent)
open import PathSum.HiddenShift.Walsh using (0ᵃ)
open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using
  (Poly; Mon; x[_]; y[_]; 1ᵐ; ⟪_⟫; _∪ᵐ_; 0ᴾ; _+ᴾ_; _-ᴾ_; κ; μ; eval)
open import PathSum.Polynomial.Decidable using (all-points?)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Reduction 3 using (elim-reduct; ½)
open import PathSum.Reduction.General 3 using (hhᴳ-reduct)
open import PathSum.Reduction.General.Decidable 3 using (hhᴳ!; elimᴳ!)
open import PathSum.Reduction.Derivation 0 public using
  (Derivation; _⟶⟨_⟩_; _≈⟨_⟩_; _≈⟨⟩_; _∎; derivation-sound)


------------------------------------------------------------------------
-- The instance

-- g(a) = a on one bit, and the shift s = (1, 0).

g₁ : Poly 1 0
g₁ = μ x[ zero ]

s₁ : Assign 2
s₁ zero       = true
s₁ (suc zero) = false

-- The path variables of the circuit, in its order: two for each
-- Hadamard layer.

private
  a b c d e h : ∀ {n} → Mon n 6
  a = ⟪ y[ zero ] ⟫
  b = ⟪ y[ suc zero ] ⟫
  c = ⟪ y[ suc (suc zero) ] ⟫
  d = ⟪ y[ suc (suc (suc zero)) ] ⟫
  e = ⟪ y[ suc (suc (suc (suc zero))) ] ⟫
  h = ⟪ y[ suc (suc (suc (suc (suc zero)))) ] ⟫


------------------------------------------------------------------------
-- The circuit on |0⟩, written out

-- ½(f′(a, b) + (a, b)·(c, d) + f̃(c, d) + (c, d)·(e, h)) with
-- f′(a, b) = g(a ⊕ 1) + (a ⊕ 1) b and f̃(c, d) = g(d) + cd, modulo 1.

Ξ₁ : PathSum 2 6 6
Ξ₁ = ⟨ (+ 4) ⋆ 1ᵐ +ᴾ (+ 4) ⋆ a +ᴾ (+ 4) ⋆ b +ᴾ (+ 4) ⋆ (a ∪ᵐ b)
       +ᴾ (+ 4) ⋆ (a ∪ᵐ c) +ᴾ (+ 4) ⋆ (b ∪ᵐ d) +ᴾ (+ 4) ⋆ d
       +ᴾ (+ 4) ⋆ (c ∪ᵐ d) +ᴾ (+ 4) ⋆ (c ∪ᵐ e) +ᴾ (+ 4) ⋆ (d ∪ᵐ h)
     , outs ⟩
  where
  outs : Fin 2 → Poly 2 6
  outs zero       = μ y[ suc (suc (suc (suc zero))) ]
  outs (suc zero) = μ y[ suc (suc (suc (suc (suc zero)))) ]

-- Its outputs are the third layer's path.

Ξ₁-outputs : ∀ x Y w → outBit Ξ₁ x Y w ≡ layer₃ 2 Y w
Ξ₁-outputs x Y zero =
  outBit-μ Ξ₁ x Y zero y[ suc (suc (suc (suc zero))) ] refl
Ξ₁-outputs x Y (suc zero) =
  outBit-μ Ξ₁ x Y (suc zero) y[ suc (suc (suc (suc (suc zero)))) ] refl

-- Its phase is ½ hs-parity modulo 1, at each of the 2^8 points.

private
  Phase : Assign 2 → Assign 6 → Set
  Phase x Y =
    pow 3 ∣ (eval (phase Ξ₁) x Y - ½ * [ hs-parity g₁ s₁ 0ᵃ Y ]ᶻ)

  Phase-resp : ∀ {x x′ Y Y′} → (∀ i → x i ≡ x′ i) → (∀ j → Y j ≡ Y′ j) →
               Phase x Y → Phase x′ Y′
  Phase-resp {x} {x′} {Y} {Y′} x≗ Y≗ = subst (pow 3 ∣_)
    (cong₂ _-_ (eval-cong (phase Ξ₁) {x} {x′} {Y} {Y′} x≗ Y≗)
               (cong (λ t → ½ * [ t ]ᶻ) (hs-parity-resp g₁ s₁ 0ᵃ Y≗)))

Ξ₁-phase : ∀ x Y → Phase x Y
Ξ₁-phase = toWitness
  {a? = all-points? Phase-resp
          (λ x Y → pow 3 ∣? (eval (phase Ξ₁) x Y
                             - ½ * [ hs-parity g₁ s₁ 0ᵃ Y ]ᶻ))}
  tt

-- So Ξ₁ is the circuit on |0⟩, in the paper's sense.

Ξ₁-circuit : Congruent (at0 (HS g₁ s₁)) Ξ₁
Ξ₁-circuit = at0-HS-congruent g₁ s₁ Ξ₁ Ξ₁-outputs Ξ₁-phase


------------------------------------------------------------------------
-- The reduction

-- [HH] at a: the quotient is ½(b + 1 + c), and 1 + c is 1 - c modulo
-- 2, whose lift is Boolean-valued; b ← 1 - c.

Q₁ : Poly 2 5
Q₁ = κ 1ℤ -ᴾ μ y[ suc zero ]

Ξ₂ : PathSum 2 6 5
Ξ₂ = hhᴳ-reduct Ξ₁ zero Q₁

-- [Elim] of b.

Ξ₃ : PathSum 2 4 4
Ξ₃ = elim-reduct Ξ₂

-- ½(c + ce + dh), outputs e h: the shift has come out of the oracle's
-- ½(a ⊕ 1)·(stuff) as the term ½c.

Λ₁ : PathSum 2 4 4
Λ₁ = ⟨ (+ 4) ⋆ ⟪ y[ zero ] ⟫
       +ᴾ (+ 4) ⋆ (⟪ y[ zero ] ⟫ ∪ᵐ ⟪ y[ suc (suc zero) ] ⟫)
       +ᴾ (+ 4) ⋆ (⟪ y[ suc zero ] ⟫ ∪ᵐ ⟪ y[ suc (suc (suc zero)) ] ⟫)
     , outs ⟩
  where
  outs : Fin 2 → Poly 2 4
  outs zero       = μ y[ suc (suc zero) ]
  outs (suc zero) = μ y[ suc (suc (suc zero)) ]

-- [HH] at c: the quotient is ½(e + 1); e ← 1.

Λ₂ : PathSum 2 4 3
Λ₂ = hhᴳ-reduct Λ₁ (suc zero) (κ 1ℤ)

-- ½dh, outputs 1 h.

Λ₃ : PathSum 2 4 3
Λ₃ = ⟨ (+ 4) ⋆ (⟪ y[ zero ] ⟫ ∪ᵐ ⟪ y[ suc (suc zero) ] ⟫) , outs ⟩
  where
  outs : Fin 2 → Poly 2 3
  outs zero       = κ 1ℤ
  outs (suc zero) = μ y[ suc (suc zero) ]

-- [HH] at d: the quotient is ½h; h ← 0.  Then [Elim] of e and of h.

Λ₄ : PathSum 2 4 2
Λ₄ = hhᴳ-reduct Λ₃ (suc zero) 0ᴾ

Λ₅ : PathSum 2 2 1
Λ₅ = elim-reduct Λ₄

Λ₆ : PathSum 2 0 0
Λ₆ = elim-reduct Λ₅

-- The circuit on |0⟩ reduces to |x⟩ ↦ |1 0⟩.

hidden-shift-derivation : Derivation (at0 (HS g₁ s₁)) (specᴾ s₁)
hidden-shift-derivation =
  at0 (HS g₁ s₁) ≈⟨ Ξ₁-circuit ⟩
  Ξ₁ ⟶⟨ hhᴳ! Ξ₁ zero Q₁ ⟩
  Ξ₂ ⟶⟨ elimᴳ! Ξ₂ ⟩
  Ξ₃ ≈⟨⟩
  Λ₁ ⟶⟨ hhᴳ! Λ₁ (suc zero) (κ 1ℤ) ⟩
  Λ₂ ≈⟨⟩
  Λ₃ ⟶⟨ hhᴳ! Λ₃ (suc zero) 0ᴾ ⟩
  Λ₄ ⟶⟨ elimᴳ! Λ₄ ⟩
  Λ₅ ⟶⟨ elimᴳ! Λ₅ ⟩
  Λ₆ ≈⟨⟩
  specᴾ s₁ ∎

hidden-shift-example : at0 (HS g₁ s₁) ≋ specᴾ s₁
hidden-shift-example = derivation-sound hidden-shift-derivation
