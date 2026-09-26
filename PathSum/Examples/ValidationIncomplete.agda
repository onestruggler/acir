------------------------------------------------------------------------
-- Presentations of groups
--
-- Translation validation is incomplete beyond Clifford circuits
--
-- PathSum.CRK.Validation formalises the translation validation of
-- section 5.1 of Amy's QPL 2018 paper, and proves it complete for
-- Clifford circuits (level at most 2): whichever normal form the
-- miter's restriction is reduced to, the circuits are equivalent
-- exactly when no path variable is left and what is left is
-- syntactically |x⟩ ↦ |x⟩.  Section 4 of the paper says that beyond
-- Clifford the reductions are incomplete.  This module is a witness
-- for translation validation itself, over the paper's own gate set
-- {H, CNOT, R_k, R_k†} and its own procedure, at level 3 (Clifford+T),
-- at the examples' precision M₀ = 0 (eighths; T = R 3).
--
-- * The circuits.  C₁ is the box of the paper's section-4 example with
--   its X gates removed (CNOT; T H T H T†; CNOT; T H T† H T†, the H and
--   T gates on the second wire).  C₂ is the inverse of another box, B₂
--   (CNOT; T† H T H T; CNOT; T† H T† H T), written out gate by gate.
--   B₂ undoes C₁ exactly, so the two circuits are equivalent
--   (equivalent, checked by computing the 4×4 matrix of the miter,
--   PathSum.CRK.Expand.equivalent!), and the miter C₁ ++ C₂ † is C₁
--   followed by B₂ (miter-is), an identity with eight Hadamards.  C₁
--   alone is not the identity (box-not-id).  Both circuits have level 3.
--   The pair was found by a search (in Python) over boxes of this
--   shape: the paper's box needs its X gates, which the gate set lacks,
--   and writing each X as H Z H would add eight Hadamards whose path
--   variables the rules would have to remove first.
--
-- * The restriction.  Gaussian elimination (PathSum.Gauss.Corollary,
--   the ⟦_⟧ᴿ Validation starts from) takes one step: it solves the last
--   Hadamard's path variable for the input x₂ and then every wire holds
--   its input (restriction).  What it reifies, ξᴿ, has normalisation
--   1/√2^8 and seven path variables, and its phase is, coefficient by
--   coefficient modulo 1 (restriction-printed), Pᴿ/8 with
--
--     Pᴿ = 2x₂ + 6x₁x₂ + y₁ + 4y₁(x₁ + x₂ + y₂) + 6x₁y₂ + 4y₂y₃ + 7y₃
--          + 4y₃(x₁ + y₄) + 6y₄ + 2x₁y₄ + 4y₄y₅ + y₅ + 4y₅(x₁ + y₆)
--          + 2x₁y₆ + 4y₆y₇ + 7y₇ + 4y₇(x₁ + x₂) ,
--
--   the paper's y₁ … y₇ being the Hadamards' path variables in circuit
--   order (Agda's variable i is the paper's y₍₇₋ᵢ₎, newest first).
--
-- * No rule of figure 2 applies to ξᴿ, at any variable or pair
--   (restriction-irreducible: the certificate of
--   PathSum.Full.Obstruction at the input x₁, read off a cheap copy of
--   the phase, PathSum.Gauss.Single).  So the only chain out of it is
--   the empty one: every reduct keeps all seven path variables
--   (only-reduct), none reaches a path-sum without path variables
--   (restriction-stuck), and the syntactic test of
--   Validation.validation-any never applies (unsettled).  Yet the
--   circuits are equivalent, and ξᴿ is the identity (restriction-id).
--   That is validation-incomplete.
--
-- * Consequences, each from the generic statements of
--   PathSum.CRK.Expand: translation validation by reduction is not
--   complete at level 3 (not-complete-3), where it is at level 2
--   (Expand.complete-2); the refutation of corollary 4.4 -- an
--   irreducible reduct with a path variable refutes -- fails at level 3
--   (not-stuck-refutes-3), where it holds at level 2
--   (Expand.stuck-refutes-2, i.e. Validation.validation-clifford-
--   refutes); so the procedure that answers no instead of expanding is
--   unsound beyond Clifford (shortcut-unsound, cf. PathSum.Expand), and
--   normal forms are not unique (normal-forms-not-unique, a second,
--   X-free witness beside PathSum.Examples.Incomplete's).  The complete
--   procedure of PathSum.Expand -- expand what reduction leaves -- is
--   what decides such a pair; running it here is not attempted (its
--   normalisation decides every rule's premises over all 2^9 monomials
--   at each of 49 renumberings, and its expansion sums 2^7 paths for
--   each of 16 entries).
--
-- Every closed statement is made through the names of
-- PathSum.CRK.Expand whose arguments are the circuits (Miter,
-- Restriction, Restricts, Equivalent, IsIdentity, Settled, ...),
-- referred to in that module itself at M₀ = 0 (E.x 0 ...), not in a
-- module application of it, and the number of path variables is spelt
-- suc 6 throughout, as the lemmas produce it: a statement written
-- otherwise is matched against the lemma proving it by computing both
-- sides, whose read-back terms are equal but not syntactically so, and
-- Agda then unfolds the substitution in the phases (50 s and 6 GB for
-- the restriction equation, minutes for restriction-id; as written,
-- the whole module checks in about 20 s).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.ValidationIncomplete where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; ⟨_,_⟩; idPS)
open import PathSum.Polynomial using (Poly; Mon; μ; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; _+ᴾ_)
open import PathSum.Examples.Base using (module CRK; _⋆_)
open import PathSum.Full 3 using (_⟶ᶠ*_; εᶠ; _◅ᶠ_)
open import PathSum.Full.Match 3 using (Irreducibleᶠ)
open import PathSum.Full.Obstruction 3 using (irreducible-stuck)

import PathSum.Congruence as Cg
import PathSum.CRK.Adjoint as Adj
import PathSum.CRK.Expand as E
import PathSum.Denotation as D
import PathSum.Expand as X

private
  variable
    k′ m′ : ℕ


------------------------------------------------------------------------
-- The circuits

-- The wires, and the gates: a CNOT from the first wire to the second,
-- and H, T = R 3 and T† = R† 3 on the second.

a b : Fin 2
a = zero
b = suc zero

CNOT₁₂ H₂ T₂ T†₂ : CRK.Gate 2
CNOT₁₂ = CRK.CNOT a b (λ ())
H₂     = CRK.H b
T₂     = CRK.R 3 b
T†₂    = CRK.R† 3 b

-- The paper's box, without its X gates.

C₁ : CRK.Circuit 2
C₁ = CNOT₁₂ ∷ T₂ ∷ H₂ ∷ T₂ ∷ H₂ ∷ T†₂ ∷
     CNOT₁₂ ∷ T₂ ∷ H₂ ∷ T†₂ ∷ H₂ ∷ T†₂ ∷ []

-- Another box, which undoes it ...

B₂ : CRK.Circuit 2
B₂ = CNOT₁₂ ∷ T†₂ ∷ H₂ ∷ T₂ ∷ H₂ ∷ T₂ ∷
     CNOT₁₂ ∷ T†₂ ∷ H₂ ∷ T†₂ ∷ H₂ ∷ T₂ ∷ []

-- ... and its inverse, gate by gate.

C₂ : CRK.Circuit 2
C₂ = T†₂ ∷ H₂ ∷ T₂ ∷ H₂ ∷ T₂ ∷ CNOT₁₂ ∷
     T†₂ ∷ H₂ ∷ T†₂ ∷ H₂ ∷ T₂ ∷ CNOT₁₂ ∷ []

C₂-inverse : C₂ ≡ Adj._† 3 B₂
C₂-inverse = refl

-- Clifford+T: level 3.

levels : CRK.level C₁ ≡ 3 × CRK.level C₂ ≡ 3
levels = refl , refl

-- The miter of section 5.1 is C₁ followed by B₂.

miter-is : E.Miter 0 C₁ C₂ ≡ C₁ ++ B₂
miter-is = refl

-- The circuits are equivalent, by the matrix of the miter; the box
-- alone is not the identity.

equivalent : E.Equivalent 0 C₁ C₂
equivalent = E.equivalent! 0 C₁ C₂

box-not-id : ¬ E.Equivalent 0 C₁ []
box-not-id = E.inequivalent! 0 C₁ []


------------------------------------------------------------------------
-- The restriction

-- One elimination step, at the second wire and its newest path
-- variable.

ξᴿ : E.Restriction 0 (E.Miter 0 C₁ C₂) (suc 6)
ξᴿ = E.restricted 0 {m = suc 6} (E.Miter 0 C₁ C₂) refl b zero

restriction : E.Restricts 0 (E.Miter 0 C₁ C₂) ξᴿ
restriction =
  E.restricted-ᴿ! 0 {m = suc 6} (E.Miter 0 C₁ C₂) refl b zero refl refl

-- Its phase, as displayed in the header: the i-th path variable is the
-- paper's y₍₇₋ᵢ₎.

private
  X₁ X₂ : Mon 2 7
  X₁ = ⟪ x[ a ] ⟫
  X₂ = ⟪ x[ b ] ⟫

  -- The paper's y₁ … y₇: Agda's path variables 6 … 0.

  y₁ y₂ y₃ y₄ y₅ y₆ y₇ : Mon 2 7
  y₁ = ⟪ y[ # 6 ] ⟫
  y₂ = ⟪ y[ # 5 ] ⟫
  y₃ = ⟪ y[ # 4 ] ⟫
  y₄ = ⟪ y[ # 3 ] ⟫
  y₅ = ⟪ y[ # 2 ] ⟫
  y₆ = ⟪ y[ # 1 ] ⟫
  y₇ = ⟪ y[ # 0 ] ⟫

Pᴿ : Poly 2 7
Pᴿ =
  (+ 2) ⋆ X₂ +ᴾ (+ 6) ⋆ (X₁ ∪ᵐ X₂) +ᴾ
  (+ 1) ⋆ y₁ +ᴾ (+ 4) ⋆ (X₁ ∪ᵐ y₁) +ᴾ (+ 4) ⋆ (X₂ ∪ᵐ y₁) +ᴾ
  (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 6) ⋆ (X₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ
  (+ 7) ⋆ y₃ +ᴾ (+ 4) ⋆ (X₁ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ
  (+ 6) ⋆ y₄ +ᴾ (+ 2) ⋆ (X₁ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (y₄ ∪ᵐ y₅) +ᴾ
  (+ 1) ⋆ y₅ +ᴾ (+ 4) ⋆ (X₁ ∪ᵐ y₅) +ᴾ (+ 4) ⋆ (y₅ ∪ᵐ y₆) +ᴾ
  (+ 2) ⋆ (X₁ ∪ᵐ y₆) +ᴾ (+ 4) ⋆ (y₆ ∪ᵐ y₇) +ᴾ
  (+ 7) ⋆ y₇ +ᴾ (+ 4) ⋆ (X₁ ∪ᵐ y₇) +ᴾ (+ 4) ⋆ (X₂ ∪ᵐ y₇)

ξˡ : PathSum 2 8 7
ξˡ = ⟨ Pᴿ , (λ w → μ x[ w ]) ⟩

restriction-printed : Cg.Congruent 0 ξᴿ ξˡ
restriction-printed =
  E.restricted-congruent! 0 {m = suc 6} (E.Miter 0 C₁ C₂) refl b zero ξˡ


------------------------------------------------------------------------
-- No rule applies to it

-- The certificate, read at the input x₁.

restriction-irreducible : Irreducibleᶠ ξᴿ
restriction-irreducible =
  E.restricted-irreducible! 0 {m = suc 6} (E.Miter 0 C₁ C₂) refl b zero a

-- So the only reduct is ξᴿ itself: every one keeps seven path
-- variables, and none has none.

only-reduct : {ζ : PathSum 2 k′ m′} → ξᴿ ⟶ᶠ* ζ → m′ ≡ 7
only-reduct εᶠ        = refl
only-reduct (s ◅ᶠ _) = ⊥-elim (restriction-irreducible s)

restriction-stuck : {ζ : PathSum 2 k′ 0} → ¬ (ξᴿ ⟶ᶠ* ζ)
restriction-stuck = irreducible-stuck ξᴿ restriction-irreducible

-- Hence validation by reduction never settles the pair ...

unsettled : ¬ E.Settled 0 C₁ C₂
unsettled = E.irreducible-unsettled 0 C₁ C₂ restriction restriction-irreducible

-- ... though the circuits are equivalent, and the restriction is the
-- identity.

restriction-id : E.IsIdentity 0 ξᴿ
restriction-id =
  E.witness-id 0 C₁ C₂ restriction restriction-irreducible equivalent

validation-incomplete :
  E.Equivalent 0 C₁ C₂ × E.Restricts 0 (E.Miter 0 C₁ C₂) ξᴿ ×
  Irreducibleᶠ ξᴿ × (∀ {k′} {ζ : PathSum 2 k′ 0} → ¬ (ξᴿ ⟶ᶠ* ζ))
validation-incomplete =
  equivalent , restriction , restriction-irreducible , restriction-stuck


------------------------------------------------------------------------
-- Consequences

-- Validation by reduction is not complete at level 3, and the
-- refutation of corollary 4.4 is unsound there.

not-complete-3 : ¬ E.Complete 0 3
not-complete-3 = E.witness-not-complete 0 C₁ C₂ restriction
  restriction-irreducible equivalent ≤-refl ≤-refl

not-stuck-refutes-3 : ¬ E.StuckRefutes 0 3
not-stuck-refutes-3 = E.witness-not-stuck-refutes 0 C₁ C₂ restriction
  restriction-irreducible equivalent ≤-refl ≤-refl

-- Answering no whenever a normal form keeps a path variable -- the
-- shortcut that is complete for Clifford path-sums -- is unsound.

shortcut-unsound :
  ¬ (∀ {n k m} (ζ : PathSum n k (suc m)) → Irreducibleᶠ ζ →
     ¬ (D._≋_ 0 ζ idPS))
shortcut-unsound = E.witness-shortcut-unsound 0 C₁ C₂ restriction
  restriction-irreducible equivalent

-- Normal forms are not unique.

normal-forms-not-unique : ¬ X.UniqueNormalForms 0
normal-forms-not-unique = E.witness-not-unique 0 C₁ C₂ restriction
  restriction-irreducible equivalent
