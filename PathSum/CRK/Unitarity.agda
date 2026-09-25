------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, CNOT, R_k, R_k†} are unitary (Amy, QPL 2018,
-- definitions 2.4 and 2.9, proposition 2.10)
--
-- PathSum.CRK.Semantics shows that the path-sum ⟦ C ⟧ of definition 2.9
-- computes the product of the gate matrices of C, a column at a time
-- (prop-2-10), and that its columns have unit trace-form norm.  This
-- module shows that the operator is unitary, in the sense of
-- PathSum.PartialIsometry.Unitary: U†U = I and UU† = I, the
-- normalisation 1/√2^k cleared, k = norm C the number of Hadamards.
-- The argument is PathSum.Unitarity's for {H , S , CZ}, over the gate
-- matrices of PathSum.Unitarity.Gates -- a Hadamard, a diagonal phase
-- for R_k and R_k†, and the permutation of a CNOT.
--
-- U†U = I.  Each gate multiplies the Hermitian product of two columns
-- by a constant (inner-gate): a Hadamard by 2, by the polarised
-- parallelogram law (inner-H); R_k and R_k† by 1, a phase common to
-- both columns cancelling (inner-R, inner-R†); and CNOT by 1, since it
-- permutes the entries -- pairing z[t≔0] with z[t≔1], swapped when
-- z_c = 1 -- which only permutes the terms of the sum (inner-CNOT).
-- So a circuit multiplies it by 2^k (inner-apply), and the columns of
-- ⟦ C ⟧, being C applied to the orthonormal basis columns, are
-- orthogonal of norm 2^k (circuit-isometry, circuit-Isometric):
-- ⟦ C ⟧ is well-formed in the sense of definition 2.4
-- (circuit-PartialIsometric).
--
-- UU† = I.  Every gate matrix is symmetric: H and the diagonal phases
-- obviously, and CNOT because its permutation is its own inverse
-- (dot-gate).  So the transpose of the matrix of C is that of
-- reverse C (dot-apply, circuit-transpose), whose columns are
-- orthonormal by the first half; they are the rows of ⟦ C ⟧
-- (circuit-coisometry).  Both halves together: circuit-Unitary.
--
-- The two departures of PathSum.CRK.Circuit carry over: CNOT carries
-- a proof that its control and target differ -- which is what makes it
-- a permutation, CNOT c c zeroing the wire -- and R k is the gate R_k
-- only for k ≤ M; for larger k it is R_M, which is unitary all the
-- same.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_; _+_; _^_)

module PathSum.CRK.Unitarity (M₀ : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (+_; -_; _*_)
open import Data.Integer.Properties using (*-identityˡ; pos-*)
open import Data.List.Base using ([]; _∷_; _++_; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; same)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-++; gateᴬ-resp; applyᴬ-resp; prop-2-10)
open import PathSum.Cyclotomic M₀ using (_≐_; _·ᴬ_; Respects)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Hermitian M₀ using
  (Σᵃ; [_]ᴬ; []ᴬ-resp; inner; inner-cong; inner-phase; inner-basis)
open import PathSum.Order M using (pow)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric)
open import PathSum.PartialIsometry.Unitary M₀ using (Coisometric; Unitary)
open import PathSum.Ring M₀ using (_⊛_; conj; ·ᴬ-cong; ·ᴬ-·ᴬ)
open import PathSum.Unitarity.Gates M₀ using
  (dot; inner-had; inner-cnot; dot-had; dot-phase; dot-cnot; dot-comm;
   dot-basis)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Normalisation

-- It counts Hadamards, so it adds up along a concatenation, and
-- reversing a circuit keeps it.

norm-++ : (C D : Circuit n) → norm (C ++ D) ≡ norm C + norm D
norm-++ []                D = refl
norm-++ (H _ ∷ C)         D = cong suc (norm-++ C D)
norm-++ (CNOT _ _ _ ∷ C)  D = norm-++ C D
norm-++ (R _ _ ∷ C)       D = norm-++ C D
norm-++ (R† _ _ ∷ C)      D = norm-++ C D

norm-reverse : (C : Circuit n) → norm (reverse C) ≡ norm C
norm-reverse []      = refl
norm-reverse (g ∷ C) =
  trans (cong norm (unfold-reverse g C))
    (trans (norm-++ (reverse C) (g ∷ []))
      (trans (cong (_+ norm (g ∷ [])) (norm-reverse C))
        (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
               (sym (norm-++ (g ∷ []) C)))))


------------------------------------------------------------------------
-- Each gate is a multiple of an isometry

-- R_k and R_k† are diagonal phases, and a common phase cancels.

inner-R : (k : ℕ) (w : Fin n) (ψ φ : Column n) →
          inner (gateᴬ (R k w) ψ) (gateᴬ (R k w) φ) ≐ inner ψ φ
inner-R k w ψ φ = inner-phase (λ z → pow (M ∸ k) * [ z w ]ᶻ) ψ φ

inner-R† : (k : ℕ) (w : Fin n) (ψ φ : Column n) →
           inner (gateᴬ (R† k w) ψ) (gateᴬ (R† k w) φ) ≐ inner ψ φ
inner-R† k w ψ φ = inner-phase (λ z → - (pow (M ∸ k) * [ z w ]ᶻ)) ψ φ

-- CNOT permutes the entries, and so only permutes the terms of the
-- sum (PathSum.Unitarity.Gates's conditional swap).

inner-CNOT : (c t : Fin n) (p : c ≢ t) {ψ φ : Column n} → Respects ψ →
             Respects φ →
             inner (gateᴬ (CNOT c t p) ψ) (gateᴬ (CNOT c t p) φ) ≐
             inner ψ φ
inner-CNOT c t p {ψ} {φ} rψ rφ = inner-cnot c t p {ψ} {φ} rψ rφ

-- A Hadamard doubles the product, as over {H , S , CZ}.

inner-H : (w : Fin n) {ψ φ : Column n} → Respects ψ → Respects φ →
          inner (gateᴬ (H w) ψ) (gateᴬ (H w) φ) ≐ (+ 2) ·ᴬ inner ψ φ
inner-H w {ψ} {φ} rψ rφ = inner-had w {ψ} {φ} rψ rφ

-- Together: every gate multiplies the product by 2^(norm g), its own
-- normalisation -- 2 for a Hadamard, 1 for the others.

inner-gate : (g : Gate n) {ψ φ : Column n} → Respects ψ → Respects φ →
             inner (gateᴬ g ψ) (gateᴬ g φ) ≐
             (+ (2 ^ norm (g ∷ []))) ·ᴬ inner ψ φ
inner-gate (H w)        rψ rφ = inner-H w rψ rφ
inner-gate (CNOT c t p) {ψ} {φ} rψ rφ i =
  trans (inner-CNOT c t p rψ rφ i) (sym (*-identityˡ (inner ψ φ i)))
inner-gate (R k w)      {ψ} {φ} _  _  i =
  trans (inner-R k w ψ φ i) (sym (*-identityˡ (inner ψ φ i)))
inner-gate (R† k w)     {ψ} {φ} _  _  i =
  trans (inner-R† k w ψ φ i) (sym (*-identityˡ (inner ψ φ i)))


------------------------------------------------------------------------
-- U†U = I

-- A circuit multiplies the product of two columns by 2^k, k the number
-- of its Hadamards.

private
  pow-norm : (g : Gate n) (C : Circuit n) →
             + (2 ^ norm C) * + (2 ^ norm (g ∷ [])) ≡ + (2 ^ norm (g ∷ C))
  pow-norm g C =
    trans (sym (pos-* (2 ^ norm C) (2 ^ norm (g ∷ []))))
      (cong +_ (trans (sym (ℕ.^-distribˡ-+-* 2 (norm C) (norm (g ∷ []))))
        (cong (2 ^_) (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
                            (sym (norm-++ (g ∷ []) C))))))

inner-apply : (C : Circuit n) {ψ φ : Column n} → Respects ψ →
              Respects φ →
              inner (applyᴬ C ψ) (applyᴬ C φ) ≐
              (+ (2 ^ norm C)) ·ᴬ inner ψ φ
inner-apply []      {ψ} {φ} rψ rφ i = sym (*-identityˡ (inner ψ φ i))
inner-apply (g ∷ C) {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ g ψ} {gateᴬ g φ}
                     (gateᴬ-resp g rψ) (gateᴬ-resp g rφ) i)
    (trans (·ᴬ-cong (+ (2 ^ norm C)) (inner-gate g rψ rφ) i)
      (trans (·ᴬ-·ᴬ (+ (2 ^ norm C)) (+ (2 ^ norm (g ∷ []))) (inner ψ φ) i)
             (cong (λ t → t * inner ψ φ i) (pow-norm g C))))

-- The columns of ⟦ C ⟧ are orthogonal, each of norm 2^k.

circuit-isometry : (C : Circuit n) (x x′ : Assign n) →
                   Σᵃ (λ z → amp ⟦ C ⟧ x z ⊛ conj (amp ⟦ C ⟧ x′ z)) ≐
                   (+ (2 ^ norm C)) ·ᴬ [ same x x′ ]ᴬ
circuit-isometry C x x′ i =
  trans (inner-cong {ψ = amp ⟦ C ⟧ x} {ψ′ = applyᴬ C (δ x)}
                    {φ = amp ⟦ C ⟧ x′} {φ′ = applyᴬ C (δ x′)}
                    (prop-2-10 C x) (prop-2-10 C x′) i)
    (trans (inner-apply C {δ x} {δ x′} ([]ᴬ-resp x) ([]ᴬ-resp x′) i)
           (·ᴬ-cong (+ (2 ^ norm C)) (inner-basis x x′) i))

-- So ⟦ C ⟧ satisfies definition 2.4.

circuit-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧
circuit-Isometric C = circuit-isometry C

circuit-PartialIsometric : (C : Circuit n) → PartialIsometric ⟦ C ⟧
circuit-PartialIsometric C =
  Isometric⇒PartialIsometric ⟦ C ⟧ (circuit-Isometric C)


------------------------------------------------------------------------
-- The transpose of a circuit's matrix

-- Every gate matrix is symmetric: a CNOT because its permutation is
-- its own inverse.

dot-gate : (g : Gate n) {ψ φ : Column n} → Respects ψ → Respects φ →
           dot (gateᴬ g ψ) φ ≐ dot ψ (gateᴬ g φ)
dot-gate (H w)        {ψ} {φ} rψ rφ = dot-had w {ψ} {φ} rψ rφ
dot-gate (CNOT c t p) {ψ} {φ} rψ rφ = dot-cnot c t p {ψ} {φ} rψ rφ
dot-gate (R k w)      {ψ} {φ} _  _  =
  dot-phase (λ z → pow (M ∸ k) * [ z w ]ᶻ) ψ φ
dot-gate (R† k w)     {ψ} {φ} _  _  =
  dot-phase (λ z → - (pow (M ∸ k) * [ z w ]ᶻ)) ψ φ

-- The gates of reverse (g ∷ C) are those of reverse C, then g.

private
  apply-reverse : (g : Gate n) (C : Circuit n) (φ : Column n) →
                  gateᴬ g (applyᴬ (reverse C) φ) ≡
                  applyᴬ (reverse (g ∷ C)) φ
  apply-reverse g C φ =
    trans (sym (applyᴬ-++ (reverse C) (g ∷ []) φ))
          (cong (λ D → applyᴬ D φ) (sym (unfold-reverse g C)))

dot-apply : (C : Circuit n) {ψ φ : Column n} → Respects ψ → Respects φ →
            dot (applyᴬ C ψ) φ ≐ dot ψ (applyᴬ (reverse C) φ)
dot-apply []      rψ rφ i = refl
dot-apply (g ∷ C) {ψ} {φ} rψ rφ i =
  trans (dot-apply C {gateᴬ g ψ} {φ} (gateᴬ-resp g rψ) rφ i)
    (trans (dot-gate g {ψ} {applyᴬ (reverse C) φ} rψ
                     (applyᴬ-resp (reverse C) rφ) i)
           (cong (λ χ → dot ψ χ i) (apply-reverse g C φ)))

-- The amplitude of ⟦ C ⟧ from x to z is that of ⟦ reverse C ⟧ from z
-- to x.

circuit-transpose : (C : Circuit n) (x z : Assign n) →
                    amp ⟦ C ⟧ x z ≐ amp ⟦ reverse C ⟧ z x
circuit-transpose C x z i =
  trans (prop-2-10 C x z i)
  (trans (sym (dot-basis {ψ = applyᴬ C (δ x)}
                         (applyᴬ-resp C (δ-resp x)) z i))
  (trans (dot-apply C {δ x} {δ z} (δ-resp x) (δ-resp z) i)
  (trans (dot-comm (δ x) (applyᴬ (reverse C) (δ z)) i)
  (trans (dot-basis {ψ = applyᴬ (reverse C) (δ z)}
                    (applyᴬ-resp (reverse C) (δ-resp z)) x i)
         (sym (prop-2-10 (reverse C) z x i))))))


------------------------------------------------------------------------
-- UU† = I

circuit-coisometry : (C : Circuit n) (z z′ : Assign n) →
                     Σᵃ (λ x → amp ⟦ C ⟧ x z ⊛ conj (amp ⟦ C ⟧ x z′)) ≐
                     (+ (2 ^ norm C)) ·ᴬ [ same z z′ ]ᴬ
circuit-coisometry C z z′ i =
  trans (inner-cong {ψ = λ x → amp ⟦ C ⟧ x z} {ψ′ = amp ⟦ reverse C ⟧ z}
                    {φ = λ x → amp ⟦ C ⟧ x z′}
                    {φ′ = amp ⟦ reverse C ⟧ z′}
                    (λ x → circuit-transpose C x z)
                    (λ x → circuit-transpose C x z′) i)
    (trans (circuit-isometry (reverse C) z z′ i)
           (cong (λ k → (+ (2 ^ k)) * [ same z z′ ]ᴬ i) (norm-reverse C)))

circuit-Coisometric : (C : Circuit n) → Coisometric ⟦ C ⟧
circuit-Coisometric C = circuit-coisometry C

-- Both halves: ⟦ C ⟧ is unitary.

circuit-Unitary : (C : Circuit n) → Unitary ⟦ C ⟧
circuit-Unitary C = circuit-Isometric C , circuit-Coisometric C
