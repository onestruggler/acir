------------------------------------------------------------------------
-- Presentations of groups
--
-- The product of multilinear polynomials
--
-- Section 2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) works in D_M[x], multilinear
-- polynomials in which x² = x.  The product there is the ordinary one
-- followed by that reduction, so the coefficient of x^γ in A · B
-- collects every way of writing γ as a union δ ∪ β, the term x^δ of A
-- meeting the term x^β of B.  PathSum.Polynomial never needed a
-- product: the lifting of a *linear* form has closed-form coefficients
-- (liftXor) and substitution was defined for those alone.  The general
-- rules of figure 2 substitute an arbitrary Boolean-valued polynomial
-- and lift arbitrary Boolean polynomials (P ⊕ Q = P + Q - 2PQ), which
-- both need _*ᴾ_.
--
-- The product is a dense double sum over all monomials, so it is meant
-- for proofs, not for computing coefficients: everything about it is
-- reached through eval-*ᴾ (evaluation is multiplicative) and, where
-- coefficients matter, Möbius inversion (PathSum.Mobius), which turns
-- statements about values back into statements about coefficients.
--
-- Also here: the monic monomial monoᴾ (named so because
-- PathSum.Circuit already exports mono) and its evaluation; the
-- evaluations of μ and 0ᴾ, which PathSum.Denotation also proves
-- (eval-μ-val, eval-0ᴾ-val) but which this layer must not load
-- Denotation to get; and reflexivity, symmetry and transitivity of
-- congruence modulo c.  The polynomials in the last three cannot be
-- inferred -- _≈[_]_ unfolds to a Π type -- so uses name them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Product where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣m∣n⇒∣m+n; ∣m⇒∣-m)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PathSum.Polynomial using
  (Mon; Poly; Var; _∪ᵐ_; _≟ᵐ_; ⟪_⟫; 0ᴾ; μ; _≈[_]_; Σsub; Σmon; satᵐ;
   eval)
open import PathSum.Polynomial.Properties using
  (Σmon-cong; Σmon-swap; Σmon-delta; Σmon-scale; Σmon-0; Σsub-cong;
   Σsub-scaleʳ; if-pullᵐ; if-swap; if-*; ⌊≟ᵐ⌋; ≡ᵐᵇ-sym; _≡ᵐᵇ_; satᵐ-∪;
   satᵐ-⟪⟫; valᵛ; i∣0)

open +-*-Solver using (solve; _:+_; _:-_; :-_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The product

-- The coefficient of γ in A · B: every splitting γ = δ ∪ β contributes
-- the product of the coefficients of δ in A and of β in B.  Overlaps
-- are allowed, which is x² = x.

infixl 7 _*ᴾ_

_*ᴾ_ : Poly n m → Poly n m → Poly n m
(A *ᴾ B) γ =
  Σmon (λ δ → Σmon (λ β → if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then A δ * B β else 0ℤ))

-- The monomial x^γ₀ as a polynomial.  The monic polynomial μ v of a
-- variable is, definitionally, the monomial ⟪ v ⟫.

monoᴾ : Mon n m → Poly n m
monoᴾ γ₀ γ = if ⌊ γ ≟ᵐ γ₀ ⌋ then 1ℤ else 0ℤ


------------------------------------------------------------------------
-- Evaluating monomials

-- A delta sum: only the monomial itself contributes.

eval-monoᴾ : (γ₀ : Mon n m) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (monoᴾ γ₀) x y ≡ (if satᵐ γ₀ x y then 1ℤ else 0ℤ)
eval-monoᴾ γ₀ x y = trans
  (Σmon-cong (λ γ → trans
    (cong (λ b → if satᵐ γ x y then (if b then 1ℤ else 0ℤ) else 0ℤ)
          (⌊≟ᵐ⌋ γ γ₀))
    (if-swap (satᵐ γ x y) (γ ≡ᵐᵇ γ₀) 1ℤ)))
  (Σmon-delta γ₀ (λ γ → if satᵐ γ x y then 1ℤ else 0ℤ))

eval-μᴾ : (v : Var n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (μ v) x y ≡ (if valᵛ v x y then 1ℤ else 0ℤ)
eval-μᴾ v x y = trans (eval-monoᴾ ⟪ v ⟫ x y)
  (cong (λ b → if b then 1ℤ else 0ℤ) (satᵐ-⟪⟫ v x y))

private
  if-0 : ∀ (b : Bool) → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0 true  = refl
  if-0 false = refl

eval-0ᴾ : (x : Fin n → Bool) (y : Fin m → Bool) → eval (0ᴾ {n} {m}) x y ≡ 0ℤ
eval-0ᴾ {n} {m} x y = trans
  (Σmon-cong {g = λ _ → 0ℤ} (λ γ → if-0 (satᵐ γ x y))) (Σmon-0 {n} {m})


------------------------------------------------------------------------
-- Evaluation is multiplicative

-- Scaling a sum on the right, from its counterpart on subsets.

Σmon-scaleʳ : ∀ {z} (f : Mon n m → ℤ) → Σmon (λ γ → f γ * z) ≡ Σmon f * z
Σmon-scaleʳ {z = z} f =
  trans (Σsub-cong (λ α → Σsub-scaleʳ {z = z} (λ β → f (α , β))))
        (Σsub-scaleʳ {z = z} (λ α → Σsub (λ β → f (α , β))))

-- The proof follows the evaluation of a substitution in
-- PathSum.Polynomial.Properties: the guard is pushed inside, the sum
-- over γ moved innermost and collapsed against the splitting δ ∪ β,
-- and what is left factors, a monomial δ ∪ β being satisfied exactly
-- when δ and β both are.

private
  term : Poly n m → Poly n m → Mon n m → Mon n m → Mon n m → ℤ
  term A B γ δ β = if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then A δ * B β else 0ℤ

  collapse : (A B : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool)
             (δ β : Mon n m) →
             Σmon (λ γ → if satᵐ γ x y then term A B γ δ β else 0ℤ) ≡
             (if satᵐ δ x y then A δ else 0ℤ) *
             (if satᵐ β x y then B β else 0ℤ)
  collapse A B x y δ β = trans (Σmon-cong step)
    (trans (Σmon-delta (δ ∪ᵐ β) (λ γ → if satᵐ γ x y then X else 0ℤ))
      (trans (cong (λ b → if b then X else 0ℤ) (satᵐ-∪ δ β x y))
             (if-* (satᵐ δ x y) (satᵐ β x y) (A δ) (B β))))
    where
    X : ℤ
    X = A δ * B β

    step : ∀ γ →
      (if satᵐ γ x y then (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then X else 0ℤ) else 0ℤ) ≡
      (if (γ ≡ᵐᵇ (δ ∪ᵐ β)) then (if satᵐ γ x y then X else 0ℤ) else 0ℤ)
    step γ = trans
      (cong (λ b → if satᵐ γ x y then (if b then X else 0ℤ) else 0ℤ)
            (trans (⌊≟ᵐ⌋ (δ ∪ᵐ β) γ) (≡ᵐᵇ-sym (δ ∪ᵐ β) γ)))
      (if-swap (satᵐ γ x y) (γ ≡ᵐᵇ (δ ∪ᵐ β)) X)

eval-*ᴾ : (A B : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (A *ᴾ B) x y ≡ eval A x y * eval B x y
eval-*ᴾ {n} {m} A B x y = trans
  -- push the guard through both inner sums
  (Σmon-cong (λ γ → sym (trans
    (Σmon-cong (λ δ → if-pullᵐ (satᵐ γ x y) (term A B γ δ)))
    (if-pullᵐ (satᵐ γ x y) (λ δ → Σmon (term A B γ δ))))))
  (trans
    -- move the γ sum innermost
    (trans (Σmon-swap (λ γ δ → Σmon (λ β → U γ δ β)))
           (Σmon-cong (λ δ → Σmon-swap (λ γ β → U γ δ β))))
    (trans
      -- collapse it against the splitting, then factor
      (Σmon-cong (λ δ → Σmon-cong (λ β → collapse A B x y δ β)))
      (trans (Σmon-cong (λ δ → Σmon-scale {z = a δ} b))
             (Σmon-scaleʳ {z = Σmon b} a))))
  where
  U : Mon n m → Mon n m → Mon n m → ℤ
  U γ δ β = if satᵐ γ x y then term A B γ δ β else 0ℤ

  a : Mon n m → ℤ
  a δ = if satᵐ δ x y then A δ else 0ℤ

  b : Mon n m → ℤ
  b β = if satᵐ β x y then B β else 0ℤ


------------------------------------------------------------------------
-- Congruence modulo c

-- _≈[ c ]_ is an equivalence relation.  Reflexivity and the other two
-- are all pointwise divisibility facts.

≈-refl : ∀ {c : ℤ} {P : Poly n m} → P ≈[ c ] P
≈-refl {c = c} {P} γ = subst (c ∣_) (sym (+-inverseʳ (P γ))) i∣0

≈-sym : ∀ {c : ℤ} {P Q : Poly n m} → P ≈[ c ] Q → Q ≈[ c ] P
≈-sym {c = c} {P} {Q} P≈Q γ =
  subst (c ∣_) (flip (P γ) (Q γ)) (∣m⇒∣-m (P≈Q γ))
  where
  flip : ∀ p q → - (p - q) ≡ q - p
  flip = solve 2 (λ p q → :- (p :- q) := q :- p) refl

≈-trans : ∀ {c : ℤ} {P Q R : Poly n m} →
          P ≈[ c ] Q → Q ≈[ c ] R → P ≈[ c ] R
≈-trans {c = c} {P} {Q} {R} P≈Q Q≈R γ =
  subst (c ∣_) (telescope (P γ) (Q γ) (R γ)) (∣m∣n⇒∣m+n (P≈Q γ) (Q≈R γ))
  where
  telescope : ∀ p q r → (p - q) + (q - r) ≡ p - r
  telescope = solve 3 (λ p q r → (p :- q) :+ (q :- r) := p :- r) refl
