------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of C† is the conjugate transpose of that of C, for
-- circuits over {H , S , CZ} (Amy, QPL 2018, sections 2.2 and 3)
--
-- PathSum.Adjoint builds C†, the gates of C inverted in the opposite
-- order, and PathSum.Miter shows that it inverts C.  Here C† is shown
-- to be the adjoint proper: the amplitude of ⟦ C† ⟧ from x to z is the
-- complex conjugate of that of ⟦ C ⟧ from z to x (circuit-adjoint),
-- conjugation being PathSum.Ring's conj, the automorphism ζ ↦ ζ⁻¹ of
-- Z[ζ].  Both path-sums have the same normalisation 1/√2^k
-- (PathSum.Adjoint's norm-†) and √2 is real, so this says that the
-- operator of ⟦ C† ⟧ is the conjugate transpose of that of ⟦ C ⟧.
--
-- Two facts combine.  The transpose: the amplitude of ⟦ C ⟧ from z to
-- x is that of ⟦ reverse C ⟧ from x to z (PathSum.Unitarity's
-- circuit-transpose; every gate matrix is symmetric).  And the
-- conjugate: inverting every gate of a circuit, in place, conjugates
-- its matrix entry by entry (conj-apply).  Gate by gate that is
-- PathSum.Adjoint.Gates: a Hadamard's sign ±1 is real, so conj passes
-- through H (conj-had); CZ's phase ζ^(½ z_w z_v) is ±1 too; and S's
-- phase ζ^(¼ z_w), conjugated, is ζ^(-¼ z_w), which is the phase of
-- S S S, the spelling of S† (rot-¼³).  The basis columns are real
-- (conj-δ), so conjugating the column C produces from |x⟩ is running
-- the inverted gates on |x⟩.  C† is reverse C with every gate
-- inverted (†-invs), whence circuit-adjoint.
--
-- No unitarity is used; together with PathSum.Unitarity's
-- circuit-Unitary this gives U_(C†) = U_C† = U_C⁻¹ for the operators.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Adjoint.Conjugate (M₀ : ℕ) where

open import Data.Bool.Base using (_∧_)
open import Data.Integer.Base using (_*_)
open import Data.List.Base using ([]; _∷_; _++_; reverse)
open import Data.List.Properties using
  (unfold-reverse; ++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M using (inv; _†)
open import PathSum.Adjoint.Gates M₀ using
  (rot-½; rot-¼³; conj-had; conj-δ)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; gateᴬ; applyᴬ; applyᴬ-cong; prop-2-10)
open import PathSum.Cyclotomic M₀ using (_≐_)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Miter M₀ using (applyᴬ-++)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Ring M₀ using (conj; conj-cong; conj-rot)
open import PathSum.Unitarity M₀ using (circuit-transpose)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Inverting the gates in place

-- Every gate of C replaced by its inverse, the order kept.

invs : Circuit n → Circuit n
invs []      = []
invs (g ∷ C) = inv g ++ invs C

invs-++ : (C D : Circuit n) → invs (C ++ D) ≡ invs C ++ invs D
invs-++ []      D = refl
invs-++ (g ∷ C) D =
  trans (cong (λ E → inv g ++ E) (invs-++ C D))
        (sym (++-assoc (inv g) (invs C) (invs D)))

-- C† is reverse C with every gate inverted.

†-invs : (C : Circuit n) → C † ≡ invs (reverse C)
†-invs []      = refl
†-invs (g ∷ C) =
  trans (cong (λ D → D ++ inv g) (†-invs C))
  (trans (cong (λ E → invs (reverse C) ++ E) (sym (++-identityʳ (inv g))))
  (trans (sym (invs-++ (reverse C) (g ∷ [])))
         (cong invs (sym (unfold-reverse g C)))))


------------------------------------------------------------------------
-- Inverting a gate conjugates its matrix

-- The inverse gate, run on the conjugate of a column, gives the
-- conjugate of the gate run on the column.

conj-gate : (g : Gate n) (ψ : Column n) →
            ∀ z → applyᴬ (inv g) (λ u → conj (ψ u)) z ≐
                  conj (gateᴬ g ψ z)
conj-gate (H w)    ψ z i = sym (conj-had w ψ z i)
conj-gate (S w)    ψ z i =
  trans (rot-¼³ (¼ * [ z w ]ᶻ) (z w) refl (conj (ψ z)) i)
        (sym (conj-rot (¼ * [ z w ]ᶻ) (ψ z) i))
conj-gate (CZ w v) ψ z i =
  trans (rot-½ (½ * [ z w ∧ z v ]ᶻ) (z w ∧ z v) refl (conj (ψ z)) i)
        (sym (conj-rot (½ * [ z w ∧ z v ]ᶻ) (ψ z) i))

-- So for a circuit: its gates inverted in place, run on the conjugate
-- of a column, give the conjugate of the circuit run on the column.

conj-apply : (C : Circuit n) (ψ : Column n) →
             ∀ z → applyᴬ (invs C) (λ u → conj (ψ u)) z ≐
                   conj (applyᴬ C ψ z)
conj-apply []      ψ z _ = refl
conj-apply (g ∷ C) ψ z i =
  trans (cong (λ F → F z i)
              (applyᴬ-++ (inv g) (invs C) (λ u → conj (ψ u))))
  (trans (applyᴬ-cong (invs C) {applyᴬ (inv g) (λ u → conj (ψ u))}
                      {λ u → conj (gateᴬ g ψ u)} (conj-gate g ψ) z i)
         (conj-apply C (gateᴬ g ψ) z i))


------------------------------------------------------------------------
-- The adjoint

-- The amplitude of ⟦ C† ⟧ from x to z is the conjugate of that of
-- ⟦ C ⟧ from z to x: its matrix, conjugated and transposed.

circuit-adjoint : (C : Circuit n) (x z : Assign n) →
                  amp ⟦ C † ⟧ x z ≐ conj (amp ⟦ C ⟧ z x)
circuit-adjoint C x z i =
  trans (prop-2-10 (C †) x z i)
  (trans (cong (λ D → applyᴬ D (δ x) z i) (†-invs C))
  (trans (applyᴬ-cong (invs (reverse C)) {δ x} {λ u → conj (δ x u)}
                      (λ u j → sym (conj-δ x u j)) z i)
  (trans (conj-apply (reverse C) (δ x) z i)
  (trans (conj-cong {a = applyᴬ (reverse C) (δ x) z}
                    {b = amp ⟦ reverse C ⟧ x z}
                    (λ j → sym (prop-2-10 (reverse C) x z j)) i)
         (conj-cong {a = amp ⟦ reverse C ⟧ x z} {b = amp ⟦ C ⟧ z x}
                    (λ j → sym (circuit-transpose C z x j)) i)))))
