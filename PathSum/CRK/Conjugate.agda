------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of C† is the conjugate transpose of that of C, for
-- circuits over {H, CNOT, R_k, R_k†} (Amy, QPL 2018, sections 2.2
-- and 3)
--
-- PathSum.CRK.Adjoint builds C†, the gates of C inverted in the
-- opposite order, and PathSum.CRK.Miter shows that it inverts C.
-- Here C† is shown to be the adjoint proper: the amplitude of ⟦ C† ⟧
-- from x to z is the complex conjugate of that of ⟦ C ⟧ from z to x
-- (circuit-adjoint), conjugation being PathSum.Ring's conj, the
-- automorphism ζ ↦ ζ⁻¹ of Z[ζ].  Both path-sums have the same
-- normalisation 1/√2^k (PathSum.CRK.Adjoint's norm-†) and √2 is real,
-- so this says that the operator of ⟦ C† ⟧ is the conjugate transpose
-- of that of ⟦ C ⟧.
--
-- The argument is PathSum.Adjoint.Conjugate's.  The transpose is
-- PathSum.CRK.Unitarity's circuit-transpose: the amplitude of ⟦ C ⟧
-- from z to x is that of ⟦ reverse C ⟧ from x to z.  The conjugate:
-- inverting every gate in place conjugates the matrix entry by entry
-- (conj-apply), gate by gate from PathSum.Adjoint.Gates -- a
-- Hadamard's sign ±1 is real (conj-had), a CNOT only moves entries
-- (conj-cnot), and R_k's phase ζ^(2^(M-k) z_w), conjugated, is the
-- phase of R_k†, and conversely (conj-phase, conj-phase⁻).  The basis
-- columns are real (conj-δ), and C† is reverse C with every gate
-- inverted (PathSum.CRK.Adjoint's †-reverse), whence circuit-adjoint.
--
-- This holds for every k, R k and R† k being read as R_M and its
-- inverse when k > M (PathSum.CRK.Circuit).  No unitarity is used;
-- with PathSum.CRK.Unitarity's circuit-Unitary it gives
-- U_(C†) = U_C† = U_C⁻¹ for the operators.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_)

module PathSum.CRK.Conjugate (M₀ : ℕ) where

open import Data.Integer.Base using (_*_)
open import Data.List.Base using ([]; _∷_; reverse; map)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint.Gates M₀ using
  (conj-had; conj-phase; conj-phase⁻; conj-δ)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.CRK.Adjoint M using (inv; _†; †-reverse)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-cong; prop-2-10)
open import PathSum.CRK.Unitarity M₀ using (circuit-transpose)
open import PathSum.Cyclotomic M₀ using (_≐_)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Order M using (pow)
open import PathSum.Ring M₀ using (conj; conj-cong)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Inverting a gate conjugates its matrix

-- The inverse gate, run on the conjugate of a column, gives the
-- conjugate of the gate run on the column.

conj-gate : (g : Gate n) (ψ : Column n) →
            ∀ z → gateᴬ (inv g) (λ u → conj (ψ u)) z ≐
                  conj (gateᴬ g ψ z)
conj-gate (H w)        ψ z i = sym (conj-had w ψ z i)
conj-gate (CNOT c t p) ψ z _ = refl
conj-gate (R k w)      ψ z i =
  sym (conj-phase (λ u → pow (M ∸ k) * [ u w ]ᶻ) ψ z i)
conj-gate (R† k w)     ψ z i =
  sym (conj-phase⁻ (λ u → pow (M ∸ k) * [ u w ]ᶻ) ψ z i)

-- So for a circuit: its gates inverted in place, run on the conjugate
-- of a column, give the conjugate of the circuit run on the column.

conj-apply : (C : Circuit n) (ψ : Column n) →
             ∀ z → applyᴬ (map inv C) (λ u → conj (ψ u)) z ≐
                   conj (applyᴬ C ψ z)
conj-apply []      ψ z _ = refl
conj-apply (g ∷ C) ψ z i =
  trans (applyᴬ-cong (map inv C) {gateᴬ (inv g) (λ u → conj (ψ u))}
                     {λ u → conj (gateᴬ g ψ u)} (conj-gate g ψ) z i)
        (conj-apply C (gateᴬ g ψ) z i)


------------------------------------------------------------------------
-- The adjoint

-- The amplitude of ⟦ C† ⟧ from x to z is the conjugate of that of
-- ⟦ C ⟧ from z to x: its matrix, conjugated and transposed.

circuit-adjoint : (C : Circuit n) (x z : Assign n) →
                  amp ⟦ C † ⟧ x z ≐ conj (amp ⟦ C ⟧ z x)
circuit-adjoint C x z i =
  trans (prop-2-10 (C †) x z i)
  (trans (cong (λ D → applyᴬ D (δ x) z i) (†-reverse C))
  (trans (applyᴬ-cong (map inv (reverse C)) {δ x} {λ u → conj (δ x u)}
                      (λ u j → sym (conj-δ x u j)) z i)
  (trans (conj-apply (reverse C) (δ x) z i)
  (trans (conj-cong {a = applyᴬ (reverse C) (δ x) z}
                    {b = amp ⟦ reverse C ⟧ x z}
                    (λ j → sym (prop-2-10 (reverse C) x z j)) i)
         (conj-cong {a = amp ⟦ reverse C ⟧ x z} {b = amp ⟦ C ⟧ z x}
                    (λ j → sym (circuit-transpose C z x j)) i)))))
