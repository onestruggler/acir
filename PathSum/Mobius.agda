------------------------------------------------------------------------
-- Presentations of groups
--
-- Möbius inversion modulo c
--
-- A multilinear polynomial is determined by its values on the Boolean
-- cube.  The map from coefficients to values is unitriangular -- the
-- value at the indicator of a set of variables is the sum of the
-- coefficients of the monomials contained in it -- so its inverse,
-- Möbius inversion on the lattice of subsets, takes integer
-- combinations of values only.  Hence if c divides every value of a
-- polynomial, it divides every coefficient.  This is what makes
-- corollary 4.4 syntactic: a path-sum with no path variables left
-- which denotes the identity has the identity's polynomials,
-- coefficient by coefficient.
--
-- The proof never writes the inverse down.  It inducts on the number
-- of variables, splitting a polynomial at its head variable x₀ as
-- P₀ + x₀ · P₁, where P₀ and P₁ are polynomials in the remaining
-- variables.  The values at x₀ = false are those of P₀, and the values
-- at x₀ = true those of P₀ + P₁; so by induction c divides every
-- coefficient of P₀, then every coefficient of P₁, and these are
-- between them all the coefficients of P.  A polynomial in both the
-- input and the path variables is handled by doing this twice, once
-- for each block of variables.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Mobius where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣m+n∣n⇒∣m)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import PathSum.Polynomial using (Poly; Mon; Σsub; sat; eval)
open import PathSum.Polynomial.Properties using
  (Σsub-0; Σsub-cong; if-∧; if-pull)

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- One block of variables

-- The value at x of the multilinear polynomial in k variables whose
-- coefficient function on the subsets of those variables is f.  An
-- evaluation of a Poly n m is two of these, nested.

evalˢ : (Subset k → ℤ) → (Fin k → Bool) → ℤ
evalˢ f x = Σsub (λ s → if sat s x then f s else 0ℤ)

-- The assignment with head b and tail x.

private
  infixr 5 _◂_

  _◂_ : Bool → (Fin k → Bool) → Fin (suc k) → Bool
  (b ◂ x) zero    = b
  (b ◂ x) (suc i) = x i

-- Splitting f at the head variable: P₀ collects the monomials without
-- it and P₁ is the quotient by it.  Setting the head to false kills
-- every monomial containing it, leaving the value of P₀; setting it to
-- true leaves the value of P₁ plus that of P₀, and that much holds by
-- computation.

evalˢ-false : (f : Subset (suc k) → ℤ) (x : Fin k → Bool) →
              evalˢ f (false ◂ x) ≡ evalˢ (λ s → f (outside ∷ s)) x
evalˢ-false {k} f x = trans
  (cong (_+ evalˢ (λ s → f (outside ∷ s)) x) (Σsub-0 {k}))
  (+-identityˡ _)

evalˢ-true : (f : Subset (suc k) → ℤ) (x : Fin k → Bool) →
             evalˢ f (true ◂ x) ≡
             evalˢ (λ s → f (inside ∷ s)) x +
             evalˢ (λ s → f (outside ∷ s)) x
evalˢ-true f x = refl

-- If c divides every value of f, it divides every value of P₀, and
-- then, by difference, every value of P₁.

private
  ∣values₀ : ∀ {c} (f : Subset (suc k) → ℤ) → (∀ x → c ∣ evalˢ f x) →
             ∀ x → c ∣ evalˢ (λ s → f (outside ∷ s)) x
  ∣values₀ {c = c} f h x =
    subst (c ∣_) (evalˢ-false f x) (h (false ◂ x))

  ∣values₁ : ∀ {c} (f : Subset (suc k) → ℤ) → (∀ x → c ∣ evalˢ f x) →
             ∀ x → c ∣ evalˢ (λ s → f (inside ∷ s)) x
  ∣values₁ {c = c} f h x = ∣m+n∣n⇒∣m
    (subst (c ∣_) (evalˢ-true f x) (h (true ◂ x)))
    (∣values₀ f h x)

-- Möbius inversion modulo c, in one block of variables.  With no
-- variables there is a single monomial, and the value at the empty
-- assignment is its coefficient.

values⇒coefficientsˢ : ∀ {k} (c : ℤ) (f : Subset k → ℤ) →
                       (∀ x → c ∣ evalˢ f x) → ∀ s → c ∣ f s
values⇒coefficientsˢ {zero}  c f h []            = h (λ ())
values⇒coefficientsˢ {suc k} c f h (outside ∷ s) =
  values⇒coefficientsˢ c (λ s → f (outside ∷ s)) (∣values₀ f h) s
values⇒coefficientsˢ {suc k} c f h (inside ∷ s)  =
  values⇒coefficientsˢ c (λ s → f (inside ∷ s)) (∣values₁ f h) s


------------------------------------------------------------------------
-- Input and path variables

-- Evaluating a polynomial in the input and path variables is
-- evaluating in the inputs the polynomial whose coefficients are its
-- evaluations in the path variables.

eval-nested : ∀ {n m} (P : Poly n m)
              (x : Fin n → Bool) (y : Fin m → Bool) →
              eval P x y ≡ evalˢ (λ α → evalˢ (λ β → P (α , β)) y) x
eval-nested P x y = Σsub-cong λ α → trans
  (Σsub-cong λ β → sym (if-∧ (sat α x) (sat β y) (P (α , β))))
  (if-pull (sat α x) (λ β → if sat β y then P (α , β) else 0ℤ))

-- Möbius inversion modulo c: applied to the input variables it gives
-- c dividing each evaluation in the path variables, and applied again
-- to the path variables it gives c dividing each coefficient.

values⇒coefficientsᵐ : ∀ {n m} (c : ℤ) (P : Poly n m) →
                       (∀ x y → c ∣ eval P x y) → ∀ γ → c ∣ P γ
values⇒coefficientsᵐ c P h (α , β) = values⇒coefficientsˢ c
  (λ β → P (α , β))
  (λ y → values⇒coefficientsˢ c (λ α → evalˢ (λ β → P (α , β)) y)
           (λ x → subst (c ∣_) (eval-nested P x y) (h x y)) α)
  β

-- The case corollary 4.4 needs: no path variables.

values⇒coefficients : ∀ {n} (c : ℤ) (P : Poly n 0) →
                      (∀ (x : Fin n → Bool) (y : Fin 0 → Bool) →
                       c ∣ eval P x y) →
                      ∀ (γ : Mon n 0) → c ∣ P γ
values⇒coefficients c P = values⇒coefficientsᵐ c P
