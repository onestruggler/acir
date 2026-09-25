------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H , S , CZ} are unitary (Amy, QPL 2018, definition 2.4
-- and proposition 2.10)
--
-- Proposition 2.10 identifies the operator of ⟦ C ⟧ with the matrix of
-- the circuit, which PathSum.CircuitSemantics builds a column at a
-- time: the column of ⟦ C ⟧ at the input x is the gates of C applied
-- in turn to the basis column δ x (prop-2-10).  Each gate acts on
-- columns by its own unnormalised matrix, a Hadamard or a diagonal
-- phase of PathSum.Unitarity.Gates, and both halves of unitarity are
-- read off those matrices.
--
-- U†U = I.  Each gate multiplies the Hermitian product of any two
-- columns (PathSum.Hermitian's inner) by a constant: S and CZ multiply
-- the entry at z by a power of ζ read off z, the same in both columns,
-- and a common phase cancels from a · conj b (inner-S, inner-CZ); a
-- Hadamard doubles the product, by the polarised parallelogram law at
-- each pair z[w≔0] , z[w≔1] (inner-H).  So a circuit multiplies it by
-- 2^k, k = norm C the number of its Hadamards (inner-apply); the basis
-- columns are orthonormal (inner-δ); and so the columns of ⟦ C ⟧ are
-- orthogonal, each of norm 2^k (circuit-isometry):
--
--   Σ_z amp ⟦ C ⟧ x z · conj (amp ⟦ C ⟧ x′ z) = 2^k [x = x′],
--
-- which is U†U = I for U the operator of ⟦ C ⟧, its entries being
-- amp ⟦ C ⟧ x z / √2^k and √2 real.  That is PathSum.PartialIsometry's
-- Isometric (circuit-Isometric), so ⟦ C ⟧ is well-formed in the sense
-- of definition 2.4 as a theorem (circuit-PartialIsometric).
--
-- UU† = I.  The matrices of H, S and CZ are symmetric (dot-gate, in
-- the unconjugated pairing dot of PathSum.Unitarity.Gates), and the
-- transpose of a product is the product of the transposes in the
-- opposite order, so the matrix of C, transposed, is that of C run
-- backwards (dot-apply): the amplitude of ⟦ C ⟧ from x to z is that of
-- ⟦ reverse C ⟧ from z to x (circuit-transpose).  The rows of ⟦ C ⟧ are
-- therefore the columns of ⟦ reverse C ⟧, which has as many Hadamards
-- (norm-reverse), and they are orthonormal by the first half
-- (circuit-coisometry):
--
--   Σ_x amp ⟦ C ⟧ x z · conj (amp ⟦ C ⟧ x z′) = 2^k [z = z′].
--
-- Both halves together: ⟦ C ⟧ is unitary (circuit-Unitary, in the sense
-- of PathSum.PartialIsometry.Unitary).  For a square matrix UU† = I
-- follows from U†U = I by linear algebra over Q(ζ), which is not
-- formalised; here it is proved from the circuit instead, through the
-- transpose, with U†U = I used only for reverse C.
--
-- The lemmas for a Hadamard, and hence those for a circuit, ask the
-- columns to respect pointwise equality of assignments, since the
-- pairing of z[w≔0] with z[w≔1] meets assignments only pointwise equal
-- to those the sum visits; the basis columns do.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _+_; _^_)

module PathSum.Unitarity (M₀ : ℕ) where

open import Data.Bool.Base using (_∧_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (+_; _*_)
open import Data.Integer.Properties using (*-identityˡ; *-comm; pos-*)
open import Data.List.Base using ([]; _∷_; _++_; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M using (norm-++)
open import PathSum.Assign using ([_]ᶻ; same)
open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; norm; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; gateᴬ; applyᴬ; prop-2-10; δ-resp; gateᴬ-resp; applyᴬ-resp)
open import PathSum.Cyclotomic M₀ using (_≐_; _·ᴬ_; Respects)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Hermitian M₀ using
  (Σᵃ; [_]ᴬ; []ᴬ-resp; inner; inner-cong; inner-phase; inner-basis)
open import PathSum.PartialIsometry M₀ using
  (Isometric; PartialIsometric; Isometric⇒PartialIsometric)
open import PathSum.PartialIsometry.Unitary M₀ using (Coisometric; Unitary)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Ring M₀ using (_⊛_; conj; ·ᴬ-cong; ·ᴬ-·ᴬ)
open import PathSum.Unitarity.Gates M₀ using
  (dot; inner-had; dot-had; dot-phase; dot-comm; dot-basis)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Each gate is a multiple of an isometry

-- S and CZ are diagonal phases, and a common phase cancels.

inner-S : (w : Fin n) (ψ φ : Column n) →
          inner (gateᴬ (S w) ψ) (gateᴬ (S w) φ) ≐ inner ψ φ
inner-S w ψ φ = inner-phase (λ z → ¼ * [ z w ]ᶻ) ψ φ

inner-CZ : (w v : Fin n) (ψ φ : Column n) →
           inner (gateᴬ (CZ w v) ψ) (gateᴬ (CZ w v) φ) ≐ inner ψ φ
inner-CZ w v ψ φ = inner-phase (λ z → ½ * [ z w ∧ z v ]ᶻ) ψ φ

-- A Hadamard on w doubles the product (PathSum.Unitarity.Gates).

inner-H : (w : Fin n) {ψ φ : Column n} → Respects ψ → Respects φ →
          inner (gateᴬ (H w) ψ) (gateᴬ (H w) φ) ≐ (+ 2) ·ᴬ inner ψ φ
inner-H w {ψ} {φ} rψ rφ = inner-had w {ψ} {φ} rψ rφ


------------------------------------------------------------------------
-- U†U = I

-- A circuit multiplies the product of two columns by 2^k, k the number
-- of its Hadamards.

inner-apply : (C : Circuit n) {ψ φ : Column n} → Respects ψ →
              Respects φ →
              inner (applyᴬ C ψ) (applyᴬ C φ) ≐
              (+ (2 ^ norm C)) ·ᴬ inner ψ φ
inner-apply []           {ψ} {φ} rψ rφ i = sym (*-identityˡ (inner ψ φ i))
inner-apply (H w ∷ C)    {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (H w) ψ} {gateᴬ (H w) φ}
                     (gateᴬ-resp (H w) rψ) (gateᴬ-resp (H w) rφ) i)
    (trans (·ᴬ-cong (+ (2 ^ norm C)) (inner-H w rψ rφ) i)
      (trans (·ᴬ-·ᴬ (+ (2 ^ norm C)) (+ 2) (inner ψ φ) i)
             (cong (λ t → t * inner ψ φ i) (twice (norm C)))))
  where
  twice : ∀ k → + (2 ^ k) * (+ 2) ≡ + (2 ^ suc k)
  twice k = trans (*-comm (+ (2 ^ k)) (+ 2)) (sym (pos-* 2 (2 ^ k)))
inner-apply (S w ∷ C)    {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (S w) ψ} {gateᴬ (S w) φ}
                     (gateᴬ-resp (S w) rψ) (gateᴬ-resp (S w) rφ) i)
        (·ᴬ-cong (+ (2 ^ norm C)) (inner-S w ψ φ) i)
inner-apply (CZ w v ∷ C) {ψ} {φ} rψ rφ i =
  trans (inner-apply C {gateᴬ (CZ w v) ψ} {gateᴬ (CZ w v) φ}
                     (gateᴬ-resp (CZ w v) rψ) (gateᴬ-resp (CZ w v) rφ) i)
        (·ᴬ-cong (+ (2 ^ norm C)) (inner-CZ w v ψ φ) i)

-- The basis columns are orthonormal: δ x is z ↦ [ same x z ]ᴬ.

inner-δ : (x x′ : Assign n) → inner (δ x) (δ x′) ≐ [ same x x′ ]ᴬ
inner-δ x x′ = inner-basis x x′

-- The columns of ⟦ C ⟧ are orthogonal, each of norm 2^k, which the
-- normalisation 1/√2^k makes 1.

circuit-isometry : (C : Circuit n) (x x′ : Assign n) →
                   Σᵃ (λ z → amp ⟦ C ⟧ x z ⊛ conj (amp ⟦ C ⟧ x′ z)) ≐
                   (+ (2 ^ norm C)) ·ᴬ [ same x x′ ]ᴬ
circuit-isometry C x x′ i =
  trans (inner-cong {ψ = amp ⟦ C ⟧ x} {ψ′ = applyᴬ C (δ x)}
                    {φ = amp ⟦ C ⟧ x′} {φ′ = applyᴬ C (δ x′)}
                    (prop-2-10 C x) (prop-2-10 C x′) i)
    (trans (inner-apply C {δ x} {δ x′} ([]ᴬ-resp x) ([]ᴬ-resp x′) i)
           (·ᴬ-cong (+ (2 ^ norm C)) (inner-δ x x′) i))

-- So ⟦ C ⟧ satisfies definition 2.4: its operator is an isometry, and
-- a fortiori a partial isometry.

circuit-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧
circuit-Isometric C = circuit-isometry C

circuit-PartialIsometric : (C : Circuit n) → PartialIsometric ⟦ C ⟧
circuit-PartialIsometric C =
  Isometric⇒PartialIsometric ⟦ C ⟧ (circuit-Isometric C)


------------------------------------------------------------------------
-- The transpose of a circuit's matrix

-- The matrices of H, S and CZ are symmetric.

dot-gate : (g : Gate n) {ψ φ : Column n} → Respects ψ → Respects φ →
           dot (gateᴬ g ψ) φ ≐ dot ψ (gateᴬ g φ)
dot-gate (H w)    {ψ} {φ} rψ rφ = dot-had w {ψ} {φ} rψ rφ
dot-gate (S w)    {ψ} {φ} _  _  = dot-phase (λ z → ¼ * [ z w ]ᶻ) ψ φ
dot-gate (CZ w v) {ψ} {φ} _  _  =
  dot-phase (λ z → ½ * [ z w ∧ z v ]ᶻ) ψ φ

-- The gates of reverse (g ∷ C) are those of reverse C, then g.

private
  applyᴬ-++ : (C D : Circuit n) (ψ : Column n) →
              applyᴬ (C ++ D) ψ ≡ applyᴬ D (applyᴬ C ψ)
  applyᴬ-++ []      D ψ = refl
  applyᴬ-++ (g ∷ C) D ψ = applyᴬ-++ C D (gateᴬ g ψ)

  apply-reverse : (g : Gate n) (C : Circuit n) (φ : Column n) →
                  gateᴬ g (applyᴬ (reverse C) φ) ≡
                  applyᴬ (reverse (g ∷ C)) φ
  apply-reverse g C φ =
    trans (sym (applyᴬ-++ (reverse C) (g ∷ []) φ))
          (cong (λ D → applyᴬ D φ) (sym (unfold-reverse g C)))

-- So the transpose of the matrix of C is that of reverse C: moved to
-- the other side of the pairing, the gates of C act last to first.

dot-apply : (C : Circuit n) {ψ φ : Column n} → Respects ψ → Respects φ →
            dot (applyᴬ C ψ) φ ≐ dot ψ (applyᴬ (reverse C) φ)
dot-apply []      rψ rφ i = refl
dot-apply (g ∷ C) {ψ} {φ} rψ rφ i =
  trans (dot-apply C {gateᴬ g ψ} {φ} (gateᴬ-resp g rψ) rφ i)
    (trans (dot-gate g {ψ} {applyᴬ (reverse C) φ} rψ
                     (applyᴬ-resp (reverse C) rφ) i)
           (cong (λ χ → dot ψ χ i) (apply-reverse g C φ)))

-- Read at two basis columns: the amplitude of ⟦ C ⟧ from x to z is that
-- of ⟦ reverse C ⟧ from z to x.

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

-- Reversing a circuit keeps its Hadamards.

norm-reverse : (C : Circuit n) → norm (reverse C) ≡ norm C
norm-reverse []      = refl
norm-reverse (g ∷ C) =
  trans (cong norm (unfold-reverse g C))
    (trans (norm-++ (reverse C) (g ∷ []))
      (trans (cong (_+ norm (g ∷ [])) (norm-reverse C))
        (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
               (sym (norm-++ (g ∷ []) C)))))


------------------------------------------------------------------------
-- UU† = I

-- The rows of ⟦ C ⟧ are the columns of ⟦ reverse C ⟧, which are
-- orthonormal by the first half.

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
