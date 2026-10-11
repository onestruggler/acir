------------------------------------------------------------------------
-- Presentations of groups
--
-- Determinants of gate matrices, for the weights of arg det_k
--
-- Definition 35 weighs a gate g on n wires by 2^{k−n} arg det ⟦ g ⟧.
-- The separators take arg det ⟦ g ⟧ from a table, in units of 2π/N
-- (π/4 for qubits); ArgDet says that the table is right: a gate's
-- value (h , M), the matrix M / r^h, has determinant x^j exactly when
-- det M = x^j r^{h dⁿ}.  The determinant is computed by evaluation,
-- by Laplace expansion along the first row of the matrix listed in the
-- order of its basis vectors.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Independence.Semantics.Quartic as Quartic

module Examples.Independence.Semantics.Determinant
  (d : ℕ) (p q : ℤ)
  (r : Quartic.Q p q)
  (r-cancel : ∀ {a b} → Quartic._*_ p q r a ≡ Quartic._*_ p q r b → a ≡ b)
  (N-1 : ℕ)
  (x^N : Quartic._^_ p q (Quartic.x p q) (suc N-1) ≡ Quartic.1q p q)
  where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base using (zero) renaming (_*_ to _*ℕ_ ; _^_ to _^ℕ_)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)

open import Examples.Independence.Semantics.Scaled d p q r r-cancel N-1 x^N

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Matrices as lists of rows

-- The digits, and the basis vectors of k qudits, in order.
digits : (m : ℕ) → List (Fin m)
digits zero    = []
digits (suc m) = zero ∷ map suc (digits m)

basis : (k : ℕ) → List (Digits k)
basis zero    = [] ∷ []
basis (suc k) = concatMap (λ a → map (a ∷_) (basis k)) (digits d)
  where
  concatMap : {A B : Set} → (A → List B) → List A → List B
  concatMap f []       = []
  concatMap f (a ∷ as) = f a ++ concatMap f as

rows : Mat k → List (List Q)
rows {k} M = map (λ i → map (λ j → ix M i j) (basis k)) (basis k)

------------------------------------------------------------------------
-- Laplace expansion along the first row

private
  -- Remove the j-th entry of a row.
  drop-at : ℕ → List Q → List Q
  drop-at _       []       = []
  drop-at zero    (_ ∷ as) = as
  drop-at (suc j) (a ∷ as) = a ∷ drop-at j as

  -- Σⱼ (−1)ʲ aⱼ det (minorⱼ), the sign alternating along the row.
  expand : (List (List Q) → Q) → ℕ → Q → List Q → List (List Q) → Q
  expand det j s []       rest = 0#
  expand det j s (a ∷ as) rest =
    s * a * det (map (drop-at j) rest) + expand det (suc j) (- s) as rest

  -- Fuelled by the number of rows.
  det′ : ℕ → List (List Q) → Q
  det′ _       []           = 1#
  det′ zero    (_ ∷ _)      = 0#
  det′ (suc n) (row ∷ rest) = expand (det′ n) 0 1# row rest

det : List (List Q) → Q
det m = det′ (length m) m
  where
  length : List (List Q) → ℕ
  length []       = 0
  length (_ ∷ as) = suc (length as)

------------------------------------------------------------------------
-- The phase of a determinant

-- The value (h , M) on k wires has determinant x^j.
ArgDet : Sc k → ℕ → Set
ArgDet {k} (h , M) j = det (rows M) ≡ x ^ j * r ^ (h *ℕ (d ^ℕ k))
