------------------------------------------------------------------------
-- Presentations of groups
--
-- Example B.1: (SH)³ = ω, and the path-sum the paper prints for it
--
-- Appendix B illustrates [ω] on the identity (SH)³ = e^{2πi/8} I that
-- motivates the rule (section 3.2):
--
--    (SH)³ : |x⟩ ↦ 1/√2³ Σ e^{2πi ⅛(4xy1 + 6y1 + 4y1y2 + 6y2 + 4y2y3
--                                     + 6y3 + 1)} |y3⟩
--          ↦ 1/√2² Σ e^{2πi ⅛(2x + 4y2x + 4y2y3 + 6y3)} |y3⟩     [ω]
--          ↦ e^{2πi ⅛(2x + 6x)} |x⟩                          [HH, Elim]
--          ↦ ω|x⟩.
--
-- The last step is an error.  2x + 6x = 8x vanishes modulo 8, so the
-- chain ends at |x⟩, not ω|x⟩, and the path-sum as printed is the
-- identity: its coefficient 6/8 on each y_i is S† (e^{2πi·¾} = -i),
-- so it is ω (S†H)³ = ω·ω̄ I = I.  The paper's intermediate lines are
-- right; only the last line and the claim are not.  Formally:
--
--  * B1ᵖ, the path-sum as printed, reduces by [ω, HH, Elim] with the
--    paper's quotients; its [ω] reduct and its final reduct agree with
--    the paper's third and last lines coefficient by coefficient, the
--    last vanishes modulo 1, and B1ᵖ ≋ idPS while ¬ (B1ᵖ ≋ ωI).
--  * SH³ᵖ, the true (SH)³ (coefficients 2/8, S, and no constant),
--    reduces by the same three rules to ωI: SH³ᵖ ≋ ωI.
--  * The circuit's own path-sum ⟦ SH³ ⟧ is SH³ᵖ with its path variables
--    renumbered (SH³-literal).  The same chain, run on it through the
--    rules at any path variable, gives ⟦ SH³ ⟧ ≋ ωI (SH³-ωᵍ), with no
--    appeal to lemma 4.1 or brute force.  Likewise ⟦ (S†H)³ ⟧ ≋ ω̄ I
--    (S†H³-ω̄ᵍ), for the circuit behind the printed coefficients.
--    (That B1ᵖ is ω times its path-sum is the explanation above, not
--    a formalised statement.)
--  * Corollary 4.4's route: on the restriction ⟦ SH³ ⟧ᴿ the last
--    Hadamard's variable is already x, and [ω, Elim] ends at ωI.
--    Lemma 4.1 at the global phase ω (PathSum.GlobalPhase) carries
--    that to the circuit, so ⟦ SH³ ⟧ ≋ ωI again (SH³-ω), and likewise
--    ⟦ (S†H)³ ⟧ ≋ ω̄ I (S†H³-ω̄).  The converse half of the same lemma
--    refutes every other phase from the same chain; for instance
--    (SH)³ is not ω̄ I (SH³-not-ω̄), its reduct's phase being ⅛.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.AppendixB where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (0ℤ; +_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,′_; proj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial
open import PathSum.Polynomial.Decidable using (by-eval; refute-by-eval)
open import PathSum.Order 3 using (pow)
open import PathSum.Reduction 3 using
  (_⟶*_; ε; _◅_; elim-reduct; ω-reduct; hh-reduct; ⅛)
open import PathSum.Reduction.Decidable 3 using
  (elim!; ω!; hh!; ωAt!; hhAt!)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere 3 using (_⟶ᵍ*_; εᵍ; _◅ᵍ_; plain)
open import PathSum.Denotation 0 using (Assign; _≋_; ≋-trans; ≋-sym)
open import PathSum.Identity 0 using (not-id-phase)
open import PathSum.Congruence 0 using
  (Congruent; congruent?;
   reduces-to-id!; reduces-to-phase!; reduces-to-phaseᵍ!)
open import PathSum.Examples.Base using
  (xᵐ; yᵐ; _⋆_; ωI; SH³; S†H³; ⟦_⟧; ⟦_⟧ᴿ; phasePS;
   circuit-renumbered-≋; circuit-phase!; corollary-4-4-phase)

private
  y∅ : Assign 0
  y∅ ()


------------------------------------------------------------------------
-- (SH)³, in the paper's variable order

-- ⅛(4xy1 + 2y1 + 4y1y2 + 2y2 + 4y2y3 + 2y3), output y3.

SH³ᵖ : PathSum 1 3 3
SH³ᵖ = ⟨ (+ 4) ⋆ (xᵐ zero ∪ᵐ yᵐ zero) +ᴾ (+ 2) ⋆ yᵐ zero
       +ᴾ (+ 4) ⋆ (yᵐ zero ∪ᵐ yᵐ (suc zero)) +ᴾ (+ 2) ⋆ yᵐ (suc zero)
       +ᴾ (+ 4) ⋆ (yᵐ (suc zero) ∪ᵐ yᵐ (suc (suc zero)))
       +ᴾ (+ 2) ⋆ yᵐ (suc (suc zero))
       , (λ _ → μ y[ suc (suc zero) ]) ⟩

-- [ω] at y1: the quotient is ¼ + ½(x ⊕ y2).

SH³ᵖ₁ : PathSum 1 2 2
SH³ᵖ₁ = ω-reduct SH³ᵖ false (xᵐ zero ∪ᵐ yᵐ zero)

-- [HH] at y2: the quotient is ½(x ⊕ y3), solving y3 = x.

SH³ᵖ₂ : PathSum 1 2 1
SH³ᵖ₂ = hh-reduct SH³ᵖ₁ zero false (xᵐ zero ∪ᵐ yᵐ zero)

-- [Elim] of the dummy y3.

SH³ᵖ₃ : PathSum 1 0 0
SH³ᵖ₃ = elim-reduct SH³ᵖ₂

SH³ᵖ-reduces : SH³ᵖ ⟶* SH³ᵖ₃
SH³ᵖ-reduces =
  ω! SH³ᵖ false (xᵐ zero ∪ᵐ yᵐ zero) ◅
  (hh! SH³ᵖ₁ zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! SH³ᵖ₂ ◅ ε))

SH³ᵖ-ω : SH³ᵖ ≋ ωI
SH³ᵖ-ω = reduces-to-phase! ⅛ SH³ᵖ-reduces


------------------------------------------------------------------------
-- The circuit (SH)³, by the paper's chain

-- ⟦ SH³ ⟧ lists y3, y2, y1.  [ω] at y1 (index 2), whose quotient is
-- ¼ + ½(x ⊕ y2), y2 being index 1 among the rest (y3, y2).

SH³ᵍ₁ : PathSum 1 2 2
SH³ᵍ₁ = ω-reduct (front (suc (suc zero)) ⟦ SH³ ⟧) false
                 (xᵐ zero ∪ᵐ yᵐ (suc zero))

-- [HH] at y2 (index 1 of y3, y2), solving y3 = x.

SH³ᵍ₂ : PathSum 1 2 1
SH³ᵍ₂ = hh-reduct (front (suc zero) SH³ᵍ₁) zero false
                  (xᵐ zero ∪ᵐ yᵐ zero)

SH³ᵍ₃ : PathSum 1 0 0
SH³ᵍ₃ = elim-reduct SH³ᵍ₂

SH³-reducesᵍ : ⟦ SH³ ⟧ ⟶ᵍ* SH³ᵍ₃
SH³-reducesᵍ =
  ωAt! ⟦ SH³ ⟧ (suc (suc zero)) false (xᵐ zero ∪ᵐ yᵐ (suc zero)) ◅ᵍ
  (hhAt! SH³ᵍ₁ (suc zero) zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ᵍ
   (plain (elim! SH³ᵍ₂) ◅ᵍ εᵍ))

SH³-ωᵍ : ⟦ SH³ ⟧ ≋ ωI
SH³-ωᵍ = reduces-to-phaseᵍ! ⅛ SH³-reducesᵍ

-- Moving y2 and then y1 to the front puts the circuit's path variables
-- in the paper's order, and then its path-sum is SH³ᵖ.

SH³-renumbered :
  Congruent (front (suc (suc zero)) (front (suc zero) ⟦ SH³ ⟧)) SH³ᵖ
SH³-renumbered = toWitness
  {a? = congruent? (front (suc (suc zero)) (front (suc zero) ⟦ SH³ ⟧))
                   SH³ᵖ}
  tt

SH³-literal : ⟦ SH³ ⟧ ≋ SH³ᵖ
SH³-literal =
  circuit-renumbered-≋ SH³ SH³ᵖ (suc zero ∷ suc (suc zero) ∷ [])
    refl refl

-- (S†H)³ = ω̄ I: the same chain, with [ω] at the quotient
-- ¾ + ½(x ⊕ y2) = ¼ + ½(1 ⊕ x ⊕ y2).

S†H³ᵍ₁ : PathSum 1 2 2
S†H³ᵍ₁ = ω-reduct (front (suc (suc zero)) ⟦ S†H³ ⟧) true
                  (xᵐ zero ∪ᵐ yᵐ (suc zero))

S†H³ᵍ₂ : PathSum 1 2 1
S†H³ᵍ₂ = hh-reduct (front (suc zero) S†H³ᵍ₁) zero false
                   (xᵐ zero ∪ᵐ yᵐ zero)

S†H³-reducesᵍ : ⟦ S†H³ ⟧ ⟶ᵍ* elim-reduct S†H³ᵍ₂
S†H³-reducesᵍ =
  ωAt! ⟦ S†H³ ⟧ (suc (suc zero)) true (xᵐ zero ∪ᵐ yᵐ (suc zero)) ◅ᵍ
  (hhAt! S†H³ᵍ₁ (suc zero) zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ᵍ
   (plain (elim! S†H³ᵍ₂) ◅ᵍ εᵍ))

S†H³-ω̄ᵍ : ⟦ S†H³ ⟧ ≋ phasePS (+ 7)
S†H³-ω̄ᵍ = reduces-to-phaseᵍ! (+ 7) S†H³-reducesᵍ


------------------------------------------------------------------------
-- The restriction, and lemma 4.1 at the phase

-- The restriction keeps the variables of the first two Hadamards, the
-- second's first.  [ω] at the second's, with quotient ¼ + ½(x ⊕ y1),
-- y1 the first's; y1 is then absent, and the phase the constant ⅛.

SH³ᴿ₁ : PathSum 1 2 1
SH³ᴿ₁ = ω-reduct ⟦ SH³ ⟧ᴿ false (xᵐ zero ∪ᵐ yᵐ zero)

SH³ᴿ₂ : PathSum 1 0 0
SH³ᴿ₂ = elim-reduct SH³ᴿ₁

SH³ᴿ-reduces : ⟦ SH³ ⟧ᴿ ⟶* SH³ᴿ₂
SH³ᴿ-reduces =
  ω! ⟦ SH³ ⟧ᴿ false (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! SH³ᴿ₁ ◅ ε)

_ : (phase SH³ᴿ₂ 1ᵐ ,′ phase SH³ᴿ₂ (xᵐ zero)) ≡ (+ 1 ,′ 0ℤ)
_ = refl

SH³ᴿ-ω : ⟦ SH³ ⟧ᴿ ≋ ωI
SH³ᴿ-ω = reduces-to-phase! ⅛ SH³ᴿ-reduces

-- Lemma 4.1 at the phase ω carries the restriction's verdict to the
-- circuit: corollary 4.4's route, ending at ω|x⟩ instead of |x⟩.

SH³-ω : ⟦ SH³ ⟧ ≋ ωI
SH³-ω = circuit-phase! SH³ ⅛ SH³ᴿ-reduces

-- The converse half: the same chain refutes every other phase.  The
-- reduct's constant is ⅛, not ⅞, so (SH)³ is not (S†H)³.

SH³-not-ω̄ : ¬ (⟦ SH³ ⟧ ≋ phasePS (+ 7))
SH³-not-ω̄ eq = refute-by-eval (phase SH³ᴿ₂) (pow 3) (κ (+ 7))
  (proj₂ (proj₂ (Equivalence.to
    (corollary-4-4-phase SH³ (+ 7) SH³ᴿ-reduces) eq)))

-- (S†H)³ by the same route; its [ω] quotient is ¾ + ½(x ⊕ y1) =
-- ¼ + ½(1 ⊕ x ⊕ y1).

S†H³ᴿ₁ : PathSum 1 2 1
S†H³ᴿ₁ = ω-reduct ⟦ S†H³ ⟧ᴿ true (xᵐ zero ∪ᵐ yᵐ zero)

S†H³ᴿ-reduces : ⟦ S†H³ ⟧ᴿ ⟶* elim-reduct S†H³ᴿ₁
S†H³ᴿ-reduces =
  ω! ⟦ S†H³ ⟧ᴿ true (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! S†H³ᴿ₁ ◅ ε)

S†H³-ω̄ : ⟦ S†H³ ⟧ ≋ phasePS (+ 7)
S†H³-ω̄ = circuit-phase! S†H³ (+ 7) S†H³ᴿ-reduces


------------------------------------------------------------------------
-- Example B.1 as printed

-- ⅛(4xy1 + 6y1 + 4y1y2 + 6y2 + 4y2y3 + 6y3 + 1), output y3.

B1ᵖ : PathSum 1 3 3
B1ᵖ = ⟨ (+ 4) ⋆ (xᵐ zero ∪ᵐ yᵐ zero) +ᴾ (+ 6) ⋆ yᵐ zero
      +ᴾ (+ 4) ⋆ (yᵐ zero ∪ᵐ yᵐ (suc zero)) +ᴾ (+ 6) ⋆ yᵐ (suc zero)
      +ᴾ (+ 4) ⋆ (yᵐ (suc zero) ∪ᵐ yᵐ (suc (suc zero)))
      +ᴾ (+ 6) ⋆ yᵐ (suc (suc zero)) +ᴾ (+ 1) ⋆ 1ᵐ
      , (λ _ → μ y[ suc (suc zero) ]) ⟩

-- The paper's quotients: ¼ + ½(y2 ⊕ 1 ⊕ x) for [ω], then ½(x ⊕ y3)
-- for [HH].

B1ᵖ₁ : PathSum 1 2 2
B1ᵖ₁ = ω-reduct B1ᵖ true (xᵐ zero ∪ᵐ yᵐ zero)

B1ᵖ₂ : PathSum 1 2 1
B1ᵖ₂ = hh-reduct B1ᵖ₁ zero false (xᵐ zero ∪ᵐ yᵐ zero)

B1ᵖ₃ : PathSum 1 0 0
B1ᵖ₃ = elim-reduct B1ᵖ₂

B1ᵖ-reduces : B1ᵖ ⟶* B1ᵖ₃
B1ᵖ-reduces =
  ω! B1ᵖ true (xᵐ zero ∪ᵐ yᵐ zero) ◅
  (hh! B1ᵖ₁ zero false (xᵐ zero ∪ᵐ yᵐ zero) ◅ (elim! B1ᵖ₂ ◅ ε))

-- The paper's third line, ⅛(2x + 4y2x + 4y2y3 + 6y3), over (y2, y3).

B1-line₃ : Poly 1 2
B1-line₃ = (+ 2) ⋆ xᵐ zero +ᴾ (+ 4) ⋆ (xᵐ zero ∪ᵐ yᵐ zero)
         +ᴾ (+ 4) ⋆ (yᵐ zero ∪ᵐ yᵐ (suc zero)) +ᴾ (+ 6) ⋆ yᵐ (suc zero)

B1-line₃-agrees : phase B1ᵖ₁ ≈[ pow 3 ] B1-line₃
B1-line₃-agrees = by-eval (phase B1ᵖ₁) (pow 3) B1-line₃

-- Its last line, ⅛(2x + 6x), which vanishes modulo 1.

B1-line₄ : Poly 1 0
B1-line₄ = (+ 2) ⋆ xᵐ zero +ᴾ (+ 6) ⋆ xᵐ zero

B1-line₄-agrees : phase B1ᵖ₃ ≈[ pow 3 ] B1-line₄
B1-line₄-agrees = by-eval (phase B1ᵖ₃) (pow 3) B1-line₄

B1-line₄-vanishes : B1-line₄ ≈[ pow 3 ] 0ᴾ
B1-line₄-vanishes = by-eval B1-line₄ (pow 3) 0ᴾ

-- So the printed path-sum is the identity ...

B1ᵖ-id : B1ᵖ ≋ idPS
B1ᵖ-id = reduces-to-id! B1ᵖ-reduces

-- ... which ω is not: its phase at x = 0 is ⅛.

ωI-not-id : ¬ (ωI ≋ idPS)
ωI-not-id = not-id-phase ωI (λ _ → false) y∅ refl
  (toWitnessFalse {a? = pow 3 ∣? eval (phase ωI) (λ _ → false) y∅} tt)

B1ᵖ-not-ω : ¬ (B1ᵖ ≋ ωI)
B1ᵖ-not-ω eq = ωI-not-id
  (≋-trans {ξ = ωI} {ζ = B1ᵖ} {χ = idPS}
     (≋-sym {ξ = B1ᵖ} {ζ = ωI} eq) B1ᵖ-id)
