------------------------------------------------------------------------
-- Presentations of groups
--
-- Verifying a circuit against a specification on the isometry
-- restriction of the miter (Amy, QPL 2018, sections 3, 4.1 and 5.2)
--
-- Section 3 checks ⟦ C ⟧ ≡ ξ through the miter ⟦ C† ⟧ ∘ ξ, and section
-- 5.2 runs that check against specifications written as path-sums,
-- whose outputs need not be linear -- the Toffoli gate's target is
-- x₃ ⊕ x₁x₂.  PathSum.CRK.Specification reduces the whole miter: the
-- isometry restriction of section 4.1 was formalised only for linear
-- outputs (PathSum.Gauss), and a composite of path-sums is not a
-- linear state.  With PathSum.Restrict it applies to the miter itself.
--
-- * spec-restriction: for a well-formed ξ, ⟦ C ⟧ ≋ ξ exactly when the
--   end of any chain of restriction steps and rules of figure 2 from
--   the miter satisfies the restriction condition (the miter is well
--   formed, ⟦ C† ⟧ being an isometry: PathSum.CRK.Miter.Compose);
--   spec-restriction-no-paths and spec-restriction-syntactic when the
--   chain ends without path variables, whatever outputs it left.
-- * spec-restriction-refutes, spec-restriction-refutes-solved: the
--   refutations of PathSum.Restrict, at the miter, with no hypothesis
--   on ξ.
-- * restricts-after: a restriction step of a composite ξ′ ∘ᴾ ξ whose
--   first factor ξ has no path variables -- a classical specification
--   such as PathSum.Toffoli.Gate.toffoliˢ -- checked on ξ′ alone, at
--   F x, F the function ξ computes, with ξ's phase read as a function
--   Φ of the input.  The composite's polynomials are built by
--   substitution and never computed (PathSum.Polynomial.Bind); its
--   values are (PathSum.Compose.Properties.eval-∘, outBit-∘), and the
--   step asks only for values.  By PathSum.Restrict.Pivot's
--   restricts-unique the reduct so checked is the paper's
--   substitution, coefficient by coefficient.  (F and Φ are
--   arguments, rather than ξ's outputs read at the empty path, so that
--   closed instances state their conditions with a cheap function:
--   written out as outBit ξ x none inside a statement about a closed
--   circuit, the spec's outputs made a one-line lemma take minutes to
--   check, against seconds with the Toffoli function.)
--
-- PathSum.Examples.Restrict carries the route out on the seven-T
-- Toffoli gate.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Restrict.Spec (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; not)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; +_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Product.Base using (_×_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Classical M₀ using (none)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using (eval-∘; outBit-∘)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.CRK.Circuit M using (Circuit; ⟦_⟧)
open import PathSum.CRK.Miter.Compose M₀ using (spec-miter-∘; miter-WellFormed)
open import PathSum.Denotation M₀ using (Assign; outBit; _≋_)
open import PathSum.Isometry M₀ using (WellFormed; Restriction-id)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; μ; x[_]; 0ᴾ; eval; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Reorder using (insertᵃ)
open import PathSum.Restrict M₀ using
  (Solved; Restricts; _⇝*_; restriction-lemma-4-1; restriction-no-paths;
   restriction-syntactic; restriction-refutes; restriction-refutes-solved)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The verdict on the restriction of the miter

spec-restriction : (C : Circuit n) (ξ : PathSum n k m) {ρ : PathSum n k′ m′} →
                   WellFormed ξ → (⟦ C † ⟧ ∘ᴾ ξ) ⇝* ρ →
                   (⟦ C ⟧ ≋ ξ ⇔ Restriction-id ρ)
spec-restriction C ξ wf steps = ⇔-trans (spec-miter-∘ C ξ)
  (restriction-lemma-4-1 (⟦ C † ⟧ ∘ᴾ ξ) (miter-WellFormed C ξ wf) steps)

spec-restriction-no-paths : (C : Circuit n) (ξ : PathSum n k m)
                            (ρ : PathSum n k′ 0) → WellFormed ξ →
                            (⟦ C † ⟧ ∘ᴾ ξ) ⇝* ρ → (⟦ C ⟧ ≋ ξ ⇔ ρ ≋ idPS)
spec-restriction-no-paths C ξ ρ wf steps = ⇔-trans (spec-miter-∘ C ξ)
  (restriction-no-paths (⟦ C † ⟧ ∘ᴾ ξ) ρ (miter-WellFormed C ξ wf) steps)

spec-restriction-syntactic : (C : Circuit n) (ξ : PathSum n k m)
                             (ρ : PathSum n k′ 0) → WellFormed ξ →
                             (⟦ C † ⟧ ∘ᴾ ξ) ⇝* ρ →
                             (⟦ C ⟧ ≋ ξ ⇔
                              (k′ ≡ 0 ×
                               (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) ×
                               phase ρ ≈[ pow M ] 0ᴾ))
spec-restriction-syntactic C ξ ρ wf steps = ⇔-trans (spec-miter-∘ C ξ)
  (restriction-syntactic (⟦ C † ⟧ ∘ᴾ ξ) ρ (miter-WellFormed C ξ wf) steps)


------------------------------------------------------------------------
-- Refutation

spec-restriction-refutes : (C : Circuit n) (ξ : PathSum n k m)
                           (ρ : PathSum n k′ m′) → (⟦ C † ⟧ ∘ᴾ ξ) ⇝* ρ →
                           (w : Fin n) (x : Assign n) →
                           (∀ y → outBit ρ x y w ≡ not (x w)) →
                           ¬ (⟦ C ⟧ ≋ ξ)
spec-restriction-refutes C ξ ρ steps w x miss eq =
  restriction-refutes (⟦ C † ⟧ ∘ᴾ ξ) ρ steps w x miss
    (Equivalence.to (spec-miter-∘ C ξ) eq)

spec-restriction-refutes-solved : (C : Circuit n) (ξ : PathSum n k m)
                                  (ρ : PathSum n k′ m′) →
                                  (⟦ C † ⟧ ∘ᴾ ξ) ⇝* ρ →
                                  (∀ w → Solved ρ w) → ¬ (ρ ≋ idPS) →
                                  ¬ (⟦ C ⟧ ≋ ξ)
spec-restriction-refutes-solved C ξ ρ steps solved ne eq =
  restriction-refutes-solved (⟦ C † ⟧ ∘ᴾ ξ) ρ steps solved ne
    (Equivalence.to (spec-miter-∘ C ξ) eq)



------------------------------------------------------------------------
-- A restriction step after a first factor without path variables

-- On a path y′ of the composite ξ′ ∘ᴾ ξ, with ξ free of path
-- variables, the outputs are ξ′'s at the input ξ sends x to, and the
-- phase is ξ's at x plus ξ′'s there (definition 2.6).  So a restriction
-- step of the composite is checked on ξ′, at F x for the function F
-- that ξ computes, and with ξ's phase read as a function Φ of the
-- input (0 for a classical specification).

private
  outBit-≗ : (ξ : PathSum n k m) {a a′ : Assign n} (y : Assign m) (w : Fin n) →
             (∀ i → a i ≡ a′ i) → outBit ξ a y w ≡ outBit ξ a′ y w
  outBit-≗ ξ {a} {a′} y w h =
    cong odd (eval-cong (out ξ w) {a} {a′} {y} {y} h (λ _ → refl))

restricts-after : (ξ′ : PathSum n k′ (suc m)) (ξ : PathSum n 0 0)
                  (F : Assign n → Assign n) (Φ : Assign n → ℤ) →
                  (∀ x w → outBit ξ x none w ≡ F x w) →
                  (∀ x → eval (phase ξ) x none ≡ Φ x) →
                  (w : Fin n) (j : Fin (suc m)) (ρ : PathSum n k′ m)
                  (keep : Assign n → Assign m → Bool) →
                  (∀ x g → outBit ξ′ (F x) (insertᵃ j (not (keep x g)) g) w ≡
                           not (x w)) →
                  (∀ x g v → outBit ρ x g v ≡
                             outBit ξ′ (F x) (insertᵃ j (keep x g) g) v) →
                  Solved ρ w →
                  (∀ x g → pow M ∣
                     (eval (phase ρ) x g -
                      (Φ x + eval (phase ξ′) (F x) (insertᵃ j (keep x g) g)))) →
                  Restricts (ξ′ ∘ᴾ ξ) w j ρ
restricts-after ξ′ ξ F Φ hF hΦ w j ρ keep miss outs solves ph = record
  { keep   = keep
  ; miss   = λ x g → trans
      (outBit-∘ ξ′ ξ x none (insertᵃ j (not (keep x g)) g) w)
      (trans (outBit-≗ ξ′ (insertᵃ j (not (keep x g)) g) w (hF x))
             (miss x g))
  ; outs   = λ x g v → trans (outs x g v) (sym (trans
      (outBit-∘ ξ′ ξ x none (insertᵃ j (keep x g) g) v)
      (outBit-≗ ξ′ (insertᵃ j (keep x g) g) v (hF x))))
  ; solves = solves
  ; phase≡ = λ x g → subst (λ e → pow M ∣ (eval (phase ρ) x g - e))
      (sym (trans (eval-∘ ξ′ ξ x none (insertᵃ j (keep x g) g))
             (cong₂ _+_ (hΦ x)
                    (eval-cong (phase ξ′) {outBit ξ x none} {F x}
                       {insertᵃ j (keep x g) g} {insertᵃ j (keep x g) g}
                       (hF x) (λ _ → refl)))))
      (ph x g)
  }
