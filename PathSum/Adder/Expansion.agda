------------------------------------------------------------------------
-- Presentations of groups
--
-- The bitwise expansion of x + y is exponentially large (Amy, QPL
-- 2018, sections 2 and 5.2)
--
-- Section 2: "the polynomial representation of a classical function
-- may grow exponentially large, as in the case of addition"; section
-- 5.2: "the size of the bitwise expansion of x + y made it difficult to
-- push to implementation sizes".  This module proves it, independently
-- of how the polynomial is written down.
--
-- The setting.  The bits of x + y, for x and y of n bits, are Boolean
-- functions of 2n variables, here interleaved -- x₀, y₀, x₁, y₁, ... --
-- so that splitting a polynomial at its first two variables splits off
-- the least significant position (dbl, ix, iy, xs, ys).  A Boolean
-- function has a unique representation as a Boolean polynomial in
-- Z₂[x, y], its algebraic normal form (a standard fact, of which only
-- the instances below are proved): every integer polynomial whose
-- values at the Boolean points have the function's parities has odd
-- coefficients exactly on the monomials of the normal form -- Möbius
-- inversion modulo 2, done here as in PathSum.Hardness.Blowup by
-- splitting at the head variables (halves, Quarters).  The theorems are
-- stated in that form, for every f : Subset (2n) → ℤ, the coefficients
-- of a polynomial in the 2n variables, whose values (evalˢ, PathSum.
-- Mobius) have the right parities.
--
-- The normal forms.  With g_i = x_i y_i and p_i = x_i ⊕ y_i, the carry
-- into position i + 1 is g_i ⊕ p_i c_i (the two never both 1), so the
-- carry out of n positions is c_n = ⊕_i g_i Π_{i<j<n} p_j.  Expanding
-- the products, its monomials are x_i y_i times one of x_j, y_j for
-- every j > i -- all distinct, 2^(n-1-i) for each i, 2^n − 1 in all.
-- The sum bit s_i = x_i ⊕ y_i ⊕ c_i has 2^i + 1.  Here the monomials
-- are the predicates cmon, smon i (and pmon i for the products
-- Π_{j<i} p_j), defined by recursion on the positions, and:
--
-- * carry-anf: every f whose values are the carry out modulo 2 has an
--   odd coefficient exactly on the monomials of cmon; sumbit-anf the
--   same for each sum bit, prop-anf for the products of propagates.
--   The carry-in is linear (carry-out-in, sumbit-in): c_n with carry-in
--   c is c_n ⊕ c·Π p_j, which is what the recursion needs.
-- * count-cmon: there are 2^n − 1 of them, in the form
--   suc (count cmon) ≡ 2 ^ n; count-smon: 2^i + 1 for the sum bit i;
--   count-pmon: 2^i.  (Also count-nonempty, the 2^k − 1 non-empty
--   monomials of k variables.)
-- * carry-terms, sumbit-terms: a polynomial written down as a list of
--   terms (monomial, integer coefficient) -- any list, in any order,
--   with any repetitions and any integer coefficients -- whose values
--   are the carry out modulo 2 has at least 2^n − 1 terms; the sum
--   bit i at least 2^i + 1.  So does any polynomial whatever, counting
--   its odd coefficients (carry-odd-count: exactly 2^n − 1) or its
--   non-zero ones (carry-support).
--
-- The theorems constrain every polynomial computing a bit; that there
-- is one is not in question -- the output polynomials of PathSum.Adder.
-- Spec's specifications compute the bits, and PathSum.Adder.Expansion.
-- PathSums reads the theorems off them, and off the output polynomials
-- of any path-sum without path variables computing the addition.
-- PathSum.Adder.Expansion.Lift does the same over the integers for the
-- carry out's Boolean-valued lift -- the form of the specifications'
-- own output polynomials -- which has (3^n − 1)/2 terms.  What is not
-- formalised: the claim's other half, that this made the paper's tool
-- slow -- a statement about its implementation and running times.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.Expansion where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject₁; fromℕ)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; s≤s)
open import Data.Nat.Properties using (+-suc)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Adder.Binary using (maj; carry-out; sumbit)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Mobius using (evalˢ)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Count using
  (count; count-cong; count-false; count-true; count-mono; _≟ˢ_;
   module Terms)
open import PathSum.Polynomial.Parity using (odd-+; odd-0; odd⇒≢0)
open import PathSum.Polynomial.Properties using (Σsub-0)

import Data.Integer.Properties as ℤ

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- Interleaved variables

-- 2n variables, x_i at 2i and y_i at 2i + 1.

dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc n) = suc (suc (dbl n))

ix iy : Fin n → Fin (dbl n)
ix {zero}  ()
ix {suc n} zero    = zero
ix {suc n} (suc i) = suc (suc (ix i))
iy {zero}  ()
iy {suc n} zero    = suc zero
iy {suc n} (suc i) = suc (suc (iy i))

-- The two operands an assignment of the 2n variables stands for.

xs ys : (Fin (dbl n) → Bool) → Fin n → Bool
xs v i = v (ix i)
ys v i = v (iy i)


------------------------------------------------------------------------
-- Propagation, and linearity in the carry-in

-- Π_{j<i} (a_j ⊕ b_j): a carry into position 0 reaches position i.

prop : (Fin n → Bool) → (Fin n → Bool) → Fin (suc n) → Bool
prop         a b zero     = true
prop {zero}  a b (suc ())
prop {suc n} a b (suc i)  =
  (a zero xor b zero) ∧ prop (λ j → a (suc j)) (λ j → b (suc j)) i

private
  -- One position: maj(a, b, c) = maj(a, b, 0) ⊕ c (a ⊕ b).

  shift-in : ∀ C P a b c →
             C xor (maj a b c ∧ P) ≡
             (C xor (maj a b false ∧ P)) xor (c ∧ ((a xor b) ∧ P))
  shift-in C P true  true  true  = sym (xor-identityʳ (C xor P))
  shift-in C P true  true  false = sym (xor-identityʳ (C xor P))
  shift-in C P true  false true  = cong (_xor P) (sym (xor-identityʳ C))
  shift-in C P true  false false = sym (xor-identityʳ (C xor false))
  shift-in C P false true  true  = cong (_xor P) (sym (xor-identityʳ C))
  shift-in C P false true  false = sym (xor-identityʳ (C xor false))
  shift-in C P false false true  = sym (xor-identityʳ (C xor false))
  shift-in C P false false false = sym (xor-identityʳ (C xor false))

  ∧-true : ∀ c → c ≡ c ∧ true
  ∧-true true  = refl
  ∧-true false = refl

  sum0-in : ∀ a b c → a xor (b xor c) ≡ (a xor (b xor false)) xor (c ∧ true)
  sum0-in true  true  true  = refl
  sum0-in true  true  false = refl
  sum0-in true  false true  = refl
  sum0-in true  false false = refl
  sum0-in false true  true  = refl
  sum0-in false true  false = refl
  sum0-in false false true  = refl
  sum0-in false false false = refl

-- The carry out with carry-in c is the one with carry-in 0, plus c if
-- every position propagates.

carry-out-in : (a b : Fin n → Bool) (c : Bool) →
               carry-out a b c ≡
               carry-out a b false xor (c ∧ prop a b (fromℕ n))
carry-out-in {zero}  a b c = ∧-true c
carry-out-in {suc n} a b c = trans
  (carry-out-in a′ b′ (maj (a zero) (b zero) c))
  (trans (shift-in (carry-out a′ b′ false) (prop a′ b′ (fromℕ n))
                   (a zero) (b zero) c)
         (cong (_xor (c ∧ ((a zero xor b zero) ∧ prop a′ b′ (fromℕ n))))
               (sym (carry-out-in a′ b′ (maj (a zero) (b zero) false)))))
  where
  a′ b′ : Fin n → Bool
  a′ j = a (suc j)
  b′ j = b (suc j)

-- Likewise each sum bit, with the propagation below it.

sumbit-in : (a b : Fin n → Bool) (c : Bool) (i : Fin n) →
            sumbit a b c i ≡ sumbit a b false i xor (c ∧ prop a b (inject₁ i))
sumbit-in {zero}  a b c ()
sumbit-in {suc n} a b c zero    = sum0-in (a zero) (b zero) c
sumbit-in {suc n} a b c (suc i) = trans
  (sumbit-in a′ b′ (maj (a zero) (b zero) c) i)
  (trans (shift-in (sumbit a′ b′ false i) (prop a′ b′ (inject₁ i))
                   (a zero) (b zero) c)
         (cong (_xor (c ∧ ((a zero xor b zero) ∧ prop a′ b′ (inject₁ i))))
               (sym (sumbit-in a′ b′ (maj (a zero) (b zero) false) i))))
  where
  a′ b′ : Fin n → Bool
  a′ j = a (suc j)
  b′ j = b (suc j)


------------------------------------------------------------------------
-- The monomials of the normal forms

-- The empty monomial, the normal form of the constant 1.

empty : Subset k → Bool
empty []            = true
empty (inside  ∷ s) = false
empty (outside ∷ s) = empty s

-- Π_{j<i} (x_j ⊕ y_j): one of x_j, y_j for each j < i, nothing above.

pmon : Fin (suc n) → Subset (dbl n) → Bool
pmon         zero     s                       = empty s
pmon {zero}  (suc ())
pmon {suc n} (suc i)  (inside  ∷ outside ∷ s) = pmon i s
pmon {suc n} (suc i)  (outside ∷ inside  ∷ s) = pmon i s
pmon {suc n} (suc i)  (inside  ∷ inside  ∷ s) = false
pmon {suc n} (suc i)  (outside ∷ outside ∷ s) = false

-- The carry out: at the lowest position present, both x_i and y_i,
-- and above it one of x_j, y_j for each j.

cmon : Subset (dbl n) → Bool
cmon {zero}  []                      = false
cmon {suc n} (outside ∷ outside ∷ s) = cmon s
cmon {suc n} (inside  ∷ inside  ∷ s) = pmon (fromℕ n) s
cmon {suc n} (inside  ∷ outside ∷ s) = false
cmon {suc n} (outside ∷ inside  ∷ s) = false

-- The sum bit i: x_i, y_i, and the monomials of the carry into i.

smon : Fin n → Subset (dbl n) → Bool
smon {zero}  ()
smon {suc n} zero    (inside  ∷ outside ∷ s) = empty s
smon {suc n} zero    (outside ∷ inside  ∷ s) = empty s
smon {suc n} zero    (inside  ∷ inside  ∷ s) = false
smon {suc n} zero    (outside ∷ outside ∷ s) = false
smon {suc n} (suc i) (outside ∷ outside ∷ s) = smon i s
smon {suc n} (suc i) (inside  ∷ inside  ∷ s) = pmon (inject₁ i) s
smon {suc n} (suc i) (inside  ∷ outside ∷ s) = false
smon {suc n} (suc i) (outside ∷ inside  ∷ s) = false


------------------------------------------------------------------------
-- Möbius inversion modulo 2, at the head variables

private
  odd-if : ∀ b z → odd (if b then z else 0ℤ) ≡ b ∧ odd z
  odd-if true  z = refl
  odd-if false z = odd-0

  xor-undo : ∀ a b → (a xor b) xor b ≡ a
  xor-undo true  true  = refl
  xor-undo true  false = refl
  xor-undo false true  = refl
  xor-undo false false = refl

  xor-cancel : ∀ {a b c d} → a xor b ≡ c → b ≡ d → a ≡ c xor d
  xor-cancel {a} {b} e₁ e₂ = trans (sym (xor-undo a b)) (cong₂ _xor_ e₁ e₂)

-- The value at b ∷ w: the part with the head variable, if b, plus the
-- part without it -- modulo 2, an exclusive or.

odd-head : (f : Subset (suc k) → ℤ) (b : Bool) (w : Fin k → Bool) →
           odd (evalˢ f (b ∷ᵃ w)) ≡
           (b ∧ odd (evalˢ (λ s → f (inside ∷ s)) w)) xor
           odd (evalˢ (λ s → f (outside ∷ s)) w)
odd-head {k} f b w =
  trans (cong odd (split b))
        (trans (odd-+ (if b then evalˢ f₁ w else 0ℤ) (evalˢ f₀ w))
               (cong (_xor odd (evalˢ f₀ w)) (odd-if b (evalˢ f₁ w))))
  where
  f₁ f₀ : Subset k → ℤ
  f₁ s = f (inside ∷ s)
  f₀ s = f (outside ∷ s)

  split : ∀ b → evalˢ f (b ∷ᵃ w) ≡
                (if b then evalˢ f₁ w else 0ℤ) +ℤ evalˢ f₀ w
  split true  = refl
  split false = cong (_+ℤ evalˢ f₀ w) (Σsub-0 {k})

-- So the values of f determine those of its two halves: the part
-- without the head variable takes the values at head 0, the quotient
-- by it the difference of the values at head 1 and head 0.

halves : (f : Subset (suc k) → ℤ) (F : (Fin (suc k) → Bool) → Bool) →
         (∀ v → odd (evalˢ f v) ≡ F v) →
         (∀ w → odd (evalˢ (λ s → f (outside ∷ s)) w) ≡ F (false ∷ᵃ w)) ×
         (∀ w → odd (evalˢ (λ s → f (inside ∷ s)) w) ≡
                F (true ∷ᵃ w) xor F (false ∷ᵃ w))
halves f F h = low , high
  where
  low : ∀ w → odd (evalˢ (λ s → f (outside ∷ s)) w) ≡ F (false ∷ᵃ w)
  low w = trans (sym (odd-head f false w)) (h (false ∷ᵃ w))

  high : ∀ w → odd (evalˢ (λ s → f (inside ∷ s)) w) ≡
               F (true ∷ᵃ w) xor F (false ∷ᵃ w)
  high w = xor-cancel (trans (sym (odd-head f true w)) (h (true ∷ᵃ w))) (low w)

-- Twice: the four quarters at the first two variables, x₀ and y₀.

module Quarters {k : ℕ} (f : Subset (suc (suc k)) → ℤ)
                (F : (Fin (suc (suc k)) → Bool) → Bool)
                (h : ∀ v → odd (evalˢ f v) ≡ F v) where

  q₀₀ : ∀ w → odd (evalˢ (λ s → f (outside ∷ outside ∷ s)) w) ≡
              F (false ∷ᵃ false ∷ᵃ w)
  q₀₀ = proj₁ (halves (λ s → f (outside ∷ s)) (λ w → F (false ∷ᵃ w))
                      (proj₁ (halves f F h)))

  q₁₀ : ∀ w → odd (evalˢ (λ s → f (inside ∷ outside ∷ s)) w) ≡
              F (true ∷ᵃ false ∷ᵃ w) xor F (false ∷ᵃ false ∷ᵃ w)
  q₁₀ = proj₁ (halves (λ s → f (inside ∷ s))
                      (λ w → F (true ∷ᵃ w) xor F (false ∷ᵃ w))
                      (proj₂ (halves f F h)))

  q₀₁ : ∀ w → odd (evalˢ (λ s → f (outside ∷ inside ∷ s)) w) ≡
              F (false ∷ᵃ true ∷ᵃ w) xor F (false ∷ᵃ false ∷ᵃ w)
  q₀₁ = proj₂ (halves (λ s → f (outside ∷ s)) (λ w → F (false ∷ᵃ w))
                      (proj₁ (halves f F h)))

  q₁₁ : ∀ w → odd (evalˢ (λ s → f (inside ∷ inside ∷ s)) w) ≡
              (F (true ∷ᵃ true ∷ᵃ w) xor F (false ∷ᵃ true ∷ᵃ w)) xor
              (F (true ∷ᵃ false ∷ᵃ w) xor F (false ∷ᵃ false ∷ᵃ w))
  q₁₁ = proj₂ (halves (λ s → f (inside ∷ s))
                      (λ w → F (true ∷ᵃ w) xor F (false ∷ᵃ w))
                      (proj₂ (halves f F h)))


------------------------------------------------------------------------
-- The normal forms

-- The constant 0 has no monomial, the constant 1 the empty one.

zero-anf : (f : Subset k → ℤ) → (∀ v → odd (evalˢ f v) ≡ false) →
           ∀ s → odd (f s) ≡ false
zero-anf {zero}  f h []            = h (λ ())
zero-anf {suc k} f h (outside ∷ s) =
  zero-anf (λ s → f (outside ∷ s)) (proj₁ (halves f (λ _ → false) h)) s
zero-anf {suc k} f h (inside  ∷ s) =
  zero-anf (λ s → f (inside ∷ s)) (proj₂ (halves f (λ _ → false) h)) s

one-anf : (f : Subset k → ℤ) → (∀ v → odd (evalˢ f v) ≡ true) →
          ∀ s → odd (f s) ≡ empty s
one-anf {zero}  f h []            = h (λ ())
one-anf {suc k} f h (outside ∷ s) =
  one-anf (λ s → f (outside ∷ s)) (proj₁ (halves f (λ _ → true) h)) s
one-anf {suc k} f h (inside  ∷ s) =
  zero-anf (λ s → f (inside ∷ s)) (proj₂ (halves f (λ _ → true) h)) s

private
  p⊕p⊕0 : ∀ p → p xor (p xor false) ≡ false
  p⊕p⊕0 true  = refl
  p⊕p⊕0 false = refl

  dup-cancel : ∀ x y → (x xor y) xor (y xor y) ≡ x xor y
  dup-cancel x y = trans (cong ((x xor y) xor_) (xor-same y))
                         (xor-identityʳ (x xor y))

  xor-back : ∀ y p → (y xor p) xor y ≡ p
  xor-back true  true  = refl
  xor-back true  false = refl
  xor-back false true  = refl
  xor-back false false = refl

-- The products of propagates.

prop-anf : (i : Fin (suc n)) (f : Subset (dbl n) → ℤ) →
           (∀ v → odd (evalˢ f v) ≡ prop (xs v) (ys v) i) →
           ∀ s → odd (f s) ≡ pmon i s
prop-anf         zero    f h s = one-anf f h s
prop-anf {zero}  (suc ())
prop-anf {suc n} (suc i) f h (outside ∷ outside ∷ s) =
  zero-anf _ (Quarters.q₀₀ f (λ v → prop (xs v) (ys v) (suc i)) h) s
prop-anf {suc n} (suc i) f h (inside  ∷ outside ∷ s) =
  prop-anf i _ (λ w → trans (Quarters.q₁₀ f F h w) (xor-identityʳ _)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → Bool
  F v = prop (xs v) (ys v) (suc i)
prop-anf {suc n} (suc i) f h (outside ∷ inside  ∷ s) =
  prop-anf i _ (λ w → trans (Quarters.q₀₁ f F h w) (xor-identityʳ _)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → Bool
  F v = prop (xs v) (ys v) (suc i)
prop-anf {suc n} (suc i) f h (inside  ∷ inside  ∷ s) =
  zero-anf _ (λ w → trans (Quarters.q₁₁ f F h w)
                          (p⊕p⊕0 (prop (xs w) (ys w) i))) s
  where
  F : (Fin (dbl (suc n)) → Bool) → Bool
  F v = prop (xs v) (ys v) (suc i)

-- The carry out.

carry-anf : (f : Subset (dbl n) → ℤ) →
            (∀ v → odd (evalˢ f v) ≡ carry-out (xs v) (ys v) false) →
            ∀ s → odd (f s) ≡ cmon s
carry-anf {zero}  f h []                      = h (λ ())
carry-anf {suc n} f h (outside ∷ outside ∷ s) =
  carry-anf _ (Quarters.q₀₀ f (λ v → carry-out (xs v) (ys v) false) h) s
carry-anf {suc n} f h (inside  ∷ outside ∷ s) =
  zero-anf _ (λ w → trans (Quarters.q₁₀ f F h w)
                          (xor-same (carry-out (xs w) (ys w) false))) s
  where
  F : (Fin (dbl (suc n)) → Bool) → Bool
  F v = carry-out (xs v) (ys v) false
carry-anf {suc n} f h (outside ∷ inside  ∷ s) =
  zero-anf _ (λ w → trans (Quarters.q₀₁ f F h w)
                          (xor-same (carry-out (xs w) (ys w) false))) s
  where
  F : (Fin (dbl (suc n)) → Bool) → Bool
  F v = carry-out (xs v) (ys v) false
carry-anf {suc n} f h (inside  ∷ inside  ∷ s) =
  prop-anf (fromℕ n) _
    (λ w → trans (Quarters.q₁₁ f (λ v → carry-out (xs v) (ys v) false) h w)
                 (diff (xs w) (ys w))) s
  where
  diff : (a b : Fin n → Bool) →
         (carry-out a b true xor carry-out a b false) xor
         (carry-out a b false xor carry-out a b false) ≡ prop a b (fromℕ n)
  diff a b = trans (dup-cancel (carry-out a b true) (carry-out a b false))
    (trans (cong (_xor carry-out a b false) (carry-out-in a b true))
           (xor-back (carry-out a b false) (prop a b (fromℕ n))))

-- The sum bits.

sumbit-anf : (i : Fin n) (f : Subset (dbl n) → ℤ) →
             (∀ v → odd (evalˢ f v) ≡ sumbit (xs v) (ys v) false i) →
             ∀ s → odd (f s) ≡ smon i s
sumbit-anf {zero}  ()
sumbit-anf {suc n} zero f h (outside ∷ outside ∷ s) =
  zero-anf _ (Quarters.q₀₀ f (λ v → sumbit (xs v) (ys v) false zero) h) s
sumbit-anf {suc n} zero f h (inside  ∷ outside ∷ s) =
  one-anf _ (Quarters.q₁₀ f (λ v → sumbit (xs v) (ys v) false zero) h) s
sumbit-anf {suc n} zero f h (outside ∷ inside  ∷ s) =
  one-anf _ (Quarters.q₀₁ f (λ v → sumbit (xs v) (ys v) false zero) h) s
sumbit-anf {suc n} zero f h (inside  ∷ inside  ∷ s) =
  zero-anf _ (Quarters.q₁₁ f (λ v → sumbit (xs v) (ys v) false zero) h) s
sumbit-anf {suc n} (suc i) f h (outside ∷ outside ∷ s) =
  sumbit-anf i _ (Quarters.q₀₀ f (λ v → sumbit (xs v) (ys v) false (suc i)) h) s
sumbit-anf {suc n} (suc i) f h (inside  ∷ outside ∷ s) =
  zero-anf _
    (λ w → trans (Quarters.q₁₀ f (λ v → sumbit (xs v) (ys v) false (suc i)) h w)
                 (xor-same (sumbit (xs w) (ys w) false i))) s
sumbit-anf {suc n} (suc i) f h (outside ∷ inside  ∷ s) =
  zero-anf _
    (λ w → trans (Quarters.q₀₁ f (λ v → sumbit (xs v) (ys v) false (suc i)) h w)
                 (xor-same (sumbit (xs w) (ys w) false i))) s
sumbit-anf {suc n} (suc i) f h (inside  ∷ inside  ∷ s) =
  prop-anf (inject₁ i) _
    (λ w → trans (Quarters.q₁₁ f (λ v → sumbit (xs v) (ys v) false (suc i)) h w)
                 (diff (xs w) (ys w))) s
  where
  diff : (a b : Fin n → Bool) →
         (sumbit a b true i xor sumbit a b false i) xor
         (sumbit a b false i xor sumbit a b false i) ≡ prop a b (inject₁ i)
  diff a b = trans (dup-cancel (sumbit a b true i) (sumbit a b false i))
    (trans (cong (_xor sumbit a b false i) (sumbit-in a b true i))
           (xor-back (sumbit a b false i) (prop a b (inject₁ i))))


------------------------------------------------------------------------
-- Counting the monomials

count-empty : count (empty {k}) ≡ 1
count-empty {zero}  = refl
count-empty {suc k} = cong₂ _+_ (count-false {k}) (count-empty {k})

private
  double : ∀ a → (0 + a) + (a + 0) ≡ 2 * a
  double = solve 1 (λ a → (con 0 :+ a) :+ (a :+ con 0) := con 2 :* a) refl

  carry-step : ∀ a c → suc ((a + 0) + (0 + c)) ≡ a + suc c
  carry-step = solve 2 (λ a c → con 1 :+ ((a :+ con 0) :+ (con 0 :+ c))
                                := a :+ (con 1 :+ c)) refl

  twice : ∀ a → a + a ≡ 2 * a
  twice = solve 1 (λ a → a :+ a := con 2 :* a) refl

  sum-step : ∀ a → (a + 0) + (0 + suc a) ≡ suc (2 * a)
  sum-step = solve 1 (λ a → (a :+ con 0) :+ (con 0 :+ (con 1 :+ a))
                           := con 1 :+ con 2 :* a) refl

-- 2^i monomials in Π_{j<i} p_j ...

count-pmon : (i : Fin (suc n)) → count (pmon i) ≡ 2 ^ toℕ i
count-pmon {n}     zero    = count-empty {dbl n}
count-pmon {suc n} (suc i) =
  trans (cong₂ _+_ (cong₂ _+_ (count-false {dbl n}) (count-pmon i))
                   (cong₂ _+_ (count-pmon i) (count-false {dbl n})))
        (double (2 ^ toℕ i))

-- ... 2^n − 1 in the carry out ...

count-cmon : suc (count (cmon {n})) ≡ 2 ^ n
count-cmon {zero}  = refl
count-cmon {suc n} = begin
  suc ((count (pmon (fromℕ n)) + count {dbl n} (λ _ → false)) +
       (count {dbl n} (λ _ → false) + count (cmon {n})))
    ≡⟨ cong suc (cong₂ _+_ (cong₂ _+_ (count-pmon (fromℕ n))
                                      (count-false {dbl n}))
                           (cong (_+ count (cmon {n})) (count-false {dbl n}))) ⟩
  suc ((2 ^ toℕ (fromℕ n) + 0) + (0 + count (cmon {n})))
    ≡⟨ cong (λ t → suc ((2 ^ t + 0) + (0 + count (cmon {n})))) (toℕ-fromℕ n) ⟩
  suc ((2 ^ n + 0) + (0 + count (cmon {n})))
    ≡⟨ carry-step (2 ^ n) (count (cmon {n})) ⟩
  2 ^ n + suc (count (cmon {n}))
    ≡⟨ cong (2 ^ n +_) (count-cmon {n}) ⟩
  2 ^ n + 2 ^ n
    ≡⟨ twice (2 ^ n) ⟩
  2 * 2 ^ n
    ∎
  where open ≡-Reasoning

-- ... and 2^i + 1 in the sum bit i.

count-smon : (i : Fin n) → count (smon i) ≡ suc (2 ^ toℕ i)
count-smon {zero}  ()
count-smon {suc n} zero    =
  cong₂ _+_ (cong₂ _+_ (count-false {dbl n}) (count-empty {dbl n}))
            (cong₂ _+_ (count-empty {dbl n}) (count-false {dbl n}))
count-smon {suc n} (suc i) = begin
  (count (pmon (inject₁ i)) + count {dbl n} (λ _ → false)) +
  (count {dbl n} (λ _ → false) + count (smon i))
    ≡⟨ cong₂ _+_ (cong₂ _+_ (count-pmon (inject₁ i)) (count-false {dbl n}))
                 (cong₂ _+_ (count-false {dbl n}) (count-smon i)) ⟩
  (2 ^ toℕ (inject₁ i) + 0) + (0 + suc (2 ^ toℕ i))
    ≡⟨ cong (λ t → (2 ^ t + 0) + (0 + suc (2 ^ toℕ i))) (toℕ-inject₁ i) ⟩
  (2 ^ toℕ i + 0) + (0 + suc (2 ^ toℕ i))
    ≡⟨ sum-step (2 ^ toℕ i) ⟩
  suc (2 * 2 ^ toℕ i)
    ∎
  where open ≡-Reasoning

-- For comparison, the 2^k − 1 non-empty monomials in k variables: the
-- normal form of x₁ ∨ … ∨ x_k, whose count PathSum.Hardness.Blowup
-- leaves in words.

count-nonempty : suc (count (λ s → not (empty {k} s))) ≡ 2 ^ k
count-nonempty {zero}  = refl
count-nonempty {suc k} =
  trans (cong (λ t → suc (t + count (λ s → not (empty {k} s))))
              (count-true {k}))
  (trans (sym (+-suc (2 ^ k) (count (λ s → not (empty {k} s)))))
  (trans (cong (2 ^ k +_) (count-nonempty {k})) (twice (2 ^ k))))


------------------------------------------------------------------------
-- Every representation is large

-- Any polynomial computing the carry out modulo 2 has exactly 2^n − 1
-- odd coefficients, and at least as many non-zero ones.

carry-odd-count : (f : Subset (dbl n) → ℤ) →
                  (∀ v → odd (evalˢ f v) ≡ carry-out (xs v) (ys v) false) →
                  suc (count (λ s → odd (f s))) ≡ 2 ^ n
carry-odd-count {n} f h =
  trans (cong suc (count-cong (carry-anf f h))) (count-cmon {n})

-- Whether an integer coefficient is non-zero.

nonzero : ℤ → Bool
nonzero z = not ⌊ z ℤ.≟ 0ℤ ⌋

carry-support : (f : Subset (dbl n) → ℤ) →
                (∀ v → odd (evalˢ f v) ≡ carry-out (xs v) (ys v) false) →
                2 ^ n ≤ suc (count (λ s → nonzero (f s)))
carry-support {n} f h = subst (_≤ suc (count (λ s → nonzero (f s))))
  (carry-odd-count f h)
  (s≤s (count-mono (λ s → odd (f s)) (λ s → nonzero (f s))
                   (λ s o → nz (f s) (odd⇒≢0 o))))
  where
  nz : ∀ z → ¬ (z ≡ 0ℤ) → nonzero z ≡ true
  nz z z≢0 with z ℤ.≟ 0ℤ
  ... | yes z≡0 = contradiction z≡0 z≢0
  ... | no  _   = refl

-- A polynomial in the 2n variables written down as a list of terms.

⟦_⟧ᵗ : List (Subset k × ℤ) → Subset k → ℤ
⟦_⟧ᵗ = Terms.⟦_⟧ᵗ _≟ˢ_

-- Whatever the list, if its values are the carry out modulo 2 it has
-- at least 2^n − 1 terms ...

carry-terms : (ts : List (Subset (dbl n) × ℤ)) →
              (∀ v → odd (evalˢ ⟦ ts ⟧ᵗ v) ≡ carry-out (xs v) (ys v) false) →
              2 ^ n ≤ suc (length ts)
carry-terms {n} ts h = subst (_≤ suc (length ts)) (count-cmon {n})
  (s≤s (Terms.terms-cover _≟ˢ_ cmon (λ s → s) (λ s t e → e) ts
          (λ s c → trans (carry-anf ⟦ ts ⟧ᵗ h s) c)))

-- ... and if they are the sum bit i, at least 2^i + 1.

sumbit-terms : (i : Fin n) (ts : List (Subset (dbl n) × ℤ)) →
               (∀ v → odd (evalˢ ⟦ ts ⟧ᵗ v) ≡ sumbit (xs v) (ys v) false i) →
               suc (2 ^ toℕ i) ≤ length ts
sumbit-terms i ts h = subst (_≤ length ts) (count-smon i)
  (Terms.terms-cover _≟ˢ_ (smon i) (λ s → s) (λ s t e → e) ts
     (λ s c → trans (sumbit-anf i ⟦ ts ⟧ᵗ h s) c))
