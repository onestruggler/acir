------------------------------------------------------------------------
-- Presentations of groups
--
-- Multilinear polynomials in the input and path variables of a
-- path-sum, following section 2 of M. Amy, "Towards Large-scale
-- Functional Verification of Universal Quantum Circuits" (QPL 2018)
--
-- A phase polynomial lives in D_M[x]/Z, the multilinear polynomials
-- with dyadic coefficients of denominator dividing 2^M, taken modulo
-- the integers.  Such a polynomial is represented here by the map
-- sending a monomial to the *numerator* of its coefficient over 2^M,
-- so that two polynomials denote the same element of D_M[x]/Z exactly
-- when their coefficients agree modulo 2^M (see _≈[_]_ below).  The
-- same type is reused for the Boolean output polynomials f, whose
-- coefficients are read modulo 2 instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; Side; inside; outside; ⁅_⁆; ⊥; _∪_; _∈_; _⊆_; ∣_∣)
  renaming (_-_ to _∖_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_; _^_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (ℕ; zero; suc; _∸_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; tabulate)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋; _×?_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Data.Bool.Properties as Bool
import Data.Fin.Subset.Properties as Subset
import Data.Nat.Base as ℕ
import Data.Product.Properties as Product
import Data.Vec.Properties as Vec

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Monomials

-- A multilinear monomial x^α y^β records which of the n input
-- variables and which of the m path variables occur in it.

Mon : ℕ → ℕ → Set
Mon n m = Subset n × Subset m

-- The constant monomial 1.

1ᵐ : Mon n m
1ᵐ = ⊥ , ⊥

-- The degree |α| of a monomial.

∥_∥ : Mon n m → ℕ
∥ α , β ∥ = ∣ α ∣ ℕ.+ ∣ β ∣

infixr 6 _∪ᵐ_

_∪ᵐ_ : Mon n m → Mon n m → Mon n m
(α , β) ∪ᵐ (α′ , β′) = α ∪ α′ , β ∪ β′

_≟ᵐ_ : DecidableEquality (Mon n m)
_≟ᵐ_ = Product.≡-dec (Vec.≡-dec Bool._≟_) (Vec.≡-dec Bool._≟_)


------------------------------------------------------------------------
-- Variables

-- x[ i ] is the i-th input variable, y[ j ] the j-th path variable.

data Var (n m : ℕ) : Set where
  x[_] : Fin n → Var n m
  y[_] : Fin m → Var n m

⟪_⟫ : Var n m → Mon n m
⟪ x[ i ] ⟫ = ⁅ i ⁆ , ⊥
⟪ y[ j ] ⟫ = ⊥ , ⁅ j ⁆

infix 4 _∈ᵐ_ _⊆ᵐ_

_∈ᵐ_ : Var n m → Mon n m → Set
x[ i ] ∈ᵐ (α , _) = i ∈ α
y[ j ] ∈ᵐ (_ , β) = j ∈ β

_∈ᵐ?_ : (v : Var n m) (γ : Mon n m) → Dec (v ∈ᵐ γ)
x[ i ] ∈ᵐ? (α , _) = i Subset.∈? α
y[ j ] ∈ᵐ? (_ , β) = j Subset.∈? β

_⊆ᵐ_ : Mon n m → Mon n m → Set
(α , β) ⊆ᵐ (α′ , β′) = (α ⊆ α′) × (β ⊆ β′)

_⊆ᵐ?_ : (γ δ : Mon n m) → Dec (γ ⊆ᵐ δ)
(α , β) ⊆ᵐ? (α′ , β′) = (α Subset.⊆? α′) ×? (β Subset.⊆? β′)

infixl 6 _∖ᵐ_

_∖ᵐ_ : Mon n m → Var n m → Mon n m
(α , β) ∖ᵐ x[ i ] = (α ∖ i) , β
(α , β) ∖ᵐ y[ j ] = α , (β ∖ j)


------------------------------------------------------------------------
-- Polynomials

-- P γ is the numerator of the coefficient of the monomial γ.

Poly : ℕ → ℕ → Set
Poly n m = Mon n m → ℤ

infixl 6 _+ᴾ_ _-ᴾ_
infixl 7 _·ᴾ_

0ᴾ : Poly n m
0ᴾ _ = 0ℤ

_+ᴾ_ : Poly n m → Poly n m → Poly n m
(P +ᴾ Q) γ = P γ + Q γ

_-ᴾ_ : Poly n m → Poly n m → Poly n m
(P -ᴾ Q) γ = P γ - Q γ

-- Multiplication by an integer scalar.

_·ᴾ_ : ℤ → Poly n m → Poly n m
(c ·ᴾ P) γ = c * P γ

-- The constant polynomial c.

κ : ℤ → Poly n m
κ c γ = if ⌊ γ ≟ᵐ 1ᵐ ⌋ then c else 0ℤ

-- The monic polynomial of a single variable.

μ : Var n m → Poly n m
μ v γ = if ⌊ γ ≟ᵐ ⟪ v ⟫ ⌋ then 1ℤ else 0ℤ

-- Two polynomials denote the same element of D[x]/(2^-M Z) exactly
-- when their coefficients agree modulo c.

infix 4 _≈[_]_

_≈[_]_ : Poly n m → ℤ → Poly n m → Set
P ≈[ c ] Q = ∀ γ → c ∣ (P γ - Q γ)

-- The variable v does not occur in P, its coefficients being read
-- modulo c.

NoVar : ℤ → Var n m → Poly n m → Set
NoVar c v P = ∀ γ → v ∈ᵐ γ → c ∣ P γ


------------------------------------------------------------------------
-- Finite sums

-- Every finite sum in this development ranges over all monomials in a
-- fixed number of variables.

Σsub : ∀ {k} → (Subset k → ℤ) → ℤ
Σsub {zero}  f = f []
Σsub {suc k} f = Σsub (λ s → f (inside ∷ s)) + Σsub (λ s → f (outside ∷ s))

Σmon : (Mon n m → ℤ) → ℤ
Σmon f = Σsub (λ α → Σsub (λ β → f (α , β)))


------------------------------------------------------------------------
-- Evaluation

-- A monomial takes the value 1 at an assignment exactly when every
-- variable occurring in it is assigned true.

sat : ∀ {k} → Subset k → (Fin k → Bool) → Bool
sat []            _ = true
sat (inside  ∷ p) f = f zero ∧ sat p (λ i → f (suc i))
sat (outside ∷ p) f = sat p (λ i → f (suc i))

satᵐ : Mon n m → (Fin n → Bool) → (Fin m → Bool) → Bool
satᵐ (α , β) x y = sat α x ∧ sat β y

-- The value of P at an assignment, as the numerator over 2^M.

eval : Poly n m → (Fin n → Bool) → (Fin m → Bool) → ℤ
eval P x y = Σmon (λ γ → if satᵐ γ x y then P γ else 0ℤ)


------------------------------------------------------------------------
-- Linear Boolean forms and their lifting

-- A Z₂-linear form  c ⊕ ⨁_{u ∈ S} u  is given by a constant c and a
-- set S of variables.  Substitution and the [ω] rule need its lifting
-- to a polynomial over D taking the same values, defined in section 2
-- by  x^α = x^α  and  P + Q = P + Q - 2PQ.  Solving that recursion
-- gives  ⨁_{u ∈ S} u = Σ_{∅ ≠ γ ⊆ S} (-2)^(|γ|-1) x^γ,  together with
-- 1 ⊕ P = 1 - P.

sgn : Bool → ℤ
sgn true  = - 1ℤ
sgn false = 1ℤ

-- (-2) ^ k, split into its sign and its magnitude.

negpow : ℕ → ℤ
negpow k = (- 1ℤ) ^ k * (+ (2 ℕ.^ k))

liftXor : Bool → Mon n m → Poly n m
liftXor c S γ =
  if ⌊ γ ≟ᵐ 1ᵐ ⌋ then (if c then 1ℤ else 0ℤ)
  else if ⌊ γ ⊆ᵐ? S ⌋ then sgn c * negpow (∥ γ ∥ ∸ 1)
  else 0ℤ

-- P [ v ← c ⊕ ⨁_{u ∈ S} u ], for a variable v not occurring in S.
-- Writing P = v · A + B with A and B free of v, the result is
-- B + A · liftXor c S; the coefficient of γ in the product collects
-- every way of splitting γ as δ ∪ β, the term  P (δ ∪ v) x^δ  of A
-- contributing  P (δ ∪ v) · (liftXor c S) β.

substTerm : Poly n m → Var n m → Bool → Mon n m → (γ δ β : Mon n m) → ℤ
substTerm P v c S γ δ β =
  if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
  else if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then P (δ ∪ᵐ ⟪ v ⟫) * liftXor c S β
  else 0ℤ

subst : Poly n m → Var n m → Bool → Mon n m → Poly n m
subst P v c S γ =
  (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ)
  + Σmon (λ δ → Σmon (substTerm P v c S γ δ))
