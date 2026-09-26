------------------------------------------------------------------------
-- Presentations of groups
--
-- The monomials of bounded degree, listed and counted (for Amy, QPL
-- 2018, corollary 2.15)
--
-- A polynomial of PathSum.Polynomial is a function on all 2^(n+m)
-- monomials in the n input and m path variables.  One of degree at
-- most d is written down by listing its coefficients on the monomials
-- of degree at most d, and monomials≤ n m d is that list of
-- monomials.  It is built by Pascal's rule: a monomial of degree at
-- most d + 1 in one more variable either contains that variable and
-- has degree at most d in the others, or does not and has degree at
-- most d + 1 in them.  This module proves the three facts the size
-- bound of corollary 2.15 needs about it; the plan of the whole
-- development is in the header of PathSum.Size.
--
--  * It lists every monomial of degree at most d exactly once and
--    nothing else.  That is stated as a sum, which is how it is used:
--    summing any g over the list is summing g over all monomials with
--    those of degree above d cut off (Σˡ-monomials≤).  So its length
--    is the number of monomials of degree at most d
--    (length-monomials≤-exact).
--  * Every entry has degree at most d (monomials≤-small).
--  * The counting lemma: there are at most (n + m + 1)^d of them
--    (length-monomials≤), since a^d + a^(d+1) ≤ (a+1)^(d+1) makes the
--    bound survive Pascal's rule.
--
-- The exact count, Σ_{i ≤ d} C(n+m, i), is here too
-- (length-monomials≤-binomial, by Pascal's rule for the binomial
-- coefficients of Data.Nat.Combinatorics); only the bound is used.
-- Sums over a list, Σˡ, are defined here, with the few laws the proofs
-- need.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Size.Monomials where

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Fin.Subset using (Subset; inside; outside; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _^_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Combinatorics using
  (_C_; nCk+nC[k+1]≡[n+1]C[k+1])
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Polynomial using (Mon; ∥_∥; Σsub; Σmon)
open import PathSum.Polynomial.Properties using
  (Σsub-0; Σsub-cong; Σmon-0; Σmon-cong)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ

private
  variable
    k n m d : ℕ
    A B : Set


------------------------------------------------------------------------
-- Sums over a list

Σˡ : List A → (A → ℤ) → ℤ
Σˡ []       f = 0ℤ
Σˡ (a ∷ as) f = f a +ℤ Σˡ as f

Σˡ-cong : (as : List A) {f g : A → ℤ} → (∀ a → f a ≡ g a) →
          Σˡ as f ≡ Σˡ as g
Σˡ-cong []       f≗g = refl
Σˡ-cong (a ∷ as) f≗g = cong₂ _+ℤ_ (f≗g a) (Σˡ-cong as f≗g)

Σˡ-++ : (as bs : List A) (f : A → ℤ) →
        Σˡ (as ++ bs) f ≡ Σˡ as f +ℤ Σˡ bs f
Σˡ-++ []       bs f = sym (ℤP.+-identityˡ (Σˡ bs f))
Σˡ-++ (a ∷ as) bs f = trans
  (cong (λ z → f a +ℤ z) (Σˡ-++ as bs f))
  (sym (ℤP.+-assoc (f a) (Σˡ as f) (Σˡ bs f)))

Σˡ-map : (h : A → B) (as : List A) (f : B → ℤ) →
         Σˡ (map h as) f ≡ Σˡ as (λ a → f (h a))
Σˡ-map h []       f = refl
Σˡ-map h (a ∷ as) f = cong (λ z → f (h a) +ℤ z) (Σˡ-map h as f)

-- Summing ones counts.

Σˡ-1 : (as : List A) → Σˡ as (λ _ → 1ℤ) ≡ + length as
Σˡ-1 []       = refl
Σˡ-1 (a ∷ as) = trans (cong (λ z → 1ℤ +ℤ z) (Σˡ-1 as))
                      (sym (ℤP.pos-+ 1 (length as)))


------------------------------------------------------------------------
-- The listing

-- The subsets of size at most d, by Pascal's rule on the head.

subsets≤ : (k d : ℕ) → List (Subset k)
subsets≤ zero    d       = [] ∷ []
subsets≤ (suc k) zero    = map (outside ∷_) (subsets≤ k zero)
subsets≤ (suc k) (suc d) =
  map (inside ∷_) (subsets≤ k d) ++ map (outside ∷_) (subsets≤ k (suc d))

-- The monomials of degree at most d: Pascal's rule on the input
-- variables, then on the path variables.

consˣ : Bool → Mon n m → Mon (suc n) m
consˣ s (α , β) = s ∷ α , β

monomials≤ : (n m d : ℕ) → List (Mon n m)
monomials≤ zero    m d       = map (λ β → [] , β) (subsets≤ m d)
monomials≤ (suc n) m zero    = map (consˣ outside) (monomials≤ n m zero)
monomials≤ (suc n) m (suc d) =
  map (consˣ inside) (monomials≤ n m d) ++
  map (consˣ outside) (monomials≤ n m (suc d))


------------------------------------------------------------------------
-- Every entry has degree at most d

subsets≤-small : ∀ k d → All (λ s → ∣ s ∣ ≤ d) (subsets≤ k d)
subsets≤-small zero    d       = z≤n ∷ []
subsets≤-small (suc k) zero    =
  AllP.map⁺ {f = outside ∷_} (subsets≤-small k zero)
subsets≤-small (suc k) (suc d) = AllP.++⁺
  (AllP.map⁺ {f = inside ∷_} (All.map s≤s (subsets≤-small k d)))
  (AllP.map⁺ {f = outside ∷_} (subsets≤-small k (suc d)))

monomials≤-small : ∀ n m d → All (λ γ → ∥ γ ∥ ≤ d) (monomials≤ n m d)
monomials≤-small zero    m d       =
  AllP.map⁺ {f = λ β → [] , β} (subsets≤-small m d)
monomials≤-small (suc n) m zero    =
  AllP.map⁺ {f = consˣ outside} (monomials≤-small n m zero)
monomials≤-small (suc n) m (suc d) = AllP.++⁺
  (AllP.map⁺ {f = consˣ inside} (All.map s≤s (monomials≤-small n m d)))
  (AllP.map⁺ {f = consˣ outside} (monomials≤-small n m (suc d)))


------------------------------------------------------------------------
-- Every monomial of degree at most d, exactly once

-- The cut-off.  Adding a variable raises the degree by one, and
-- suc a ≤ᵇ suc b is a ≤ᵇ b, though not definitionally.

cut : ℕ → ℕ → ℤ → ℤ
cut d s z = if s ≤ᵇ d then z else 0ℤ

≤ᵇ-suc : ∀ a b → (suc a ≤ᵇ suc b) ≡ (a ≤ᵇ b)
≤ᵇ-suc zero    b = refl
≤ᵇ-suc (suc a) b = refl

cut-suc : ∀ d s z → cut (suc d) (suc s) z ≡ cut d s z
cut-suc d s z = cong (λ b → if b then z else 0ℤ) (≤ᵇ-suc s d)

-- Summing over the listing is summing over all subsets, cut off above
-- degree d.

Σˡ-subsets≤ : ∀ k d (g : Subset k → ℤ) →
              Σˡ (subsets≤ k d) g ≡ Σsub (λ s → cut d ∣ s ∣ (g s))
Σˡ-subsets≤ zero    d       g = ℤP.+-identityʳ (g [])
Σˡ-subsets≤ (suc k) zero    g = trans
  (Σˡ-map (outside ∷_) (subsets≤ k zero) g)
  (trans (Σˡ-subsets≤ k zero (λ s → g (outside ∷ s)))
         (sym (trans (cong (_+ℤ rest) (Σsub-0 {k}))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σsub (λ s → cut zero ∣ s ∣ (g (outside ∷ s)))
Σˡ-subsets≤ (suc k) (suc d) g = trans
  (Σˡ-++ (map (inside ∷_) (subsets≤ k d))
         (map (outside ∷_) (subsets≤ k (suc d))) g)
  (cong₂ _+ℤ_
    (trans (Σˡ-map (inside ∷_) (subsets≤ k d) g)
      (trans (Σˡ-subsets≤ k d (λ s → g (inside ∷ s)))
             (Σsub-cong (λ s → sym (cut-suc d ∣ s ∣ (g (inside ∷ s)))))))
    (trans (Σˡ-map (outside ∷_) (subsets≤ k (suc d)) g)
           (Σˡ-subsets≤ k (suc d) (λ s → g (outside ∷ s)))))

-- And for monomials.

Σˡ-monomials≤ : ∀ n m d (g : Mon n m → ℤ) →
                Σˡ (monomials≤ n m d) g ≡
                Σmon (λ γ → cut d ∥ γ ∥ (g γ))
Σˡ-monomials≤ zero    m d       g = trans
  (Σˡ-map (λ β → [] , β) (subsets≤ m d) g)
  (Σˡ-subsets≤ m d (λ β → g ([] , β)))
Σˡ-monomials≤ (suc n) m zero    g = trans
  (Σˡ-map (consˣ outside) (monomials≤ n m zero) g)
  (trans (Σˡ-monomials≤ n m zero (λ γ → g (consˣ outside γ)))
         (sym (trans (cong (_+ℤ rest) (Σmon-0 {n} {m}))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σmon (λ γ → cut zero ∥ γ ∥ (g (consˣ outside γ)))
Σˡ-monomials≤ (suc n) m (suc d) g = trans
  (Σˡ-++ (map (consˣ inside) (monomials≤ n m d))
         (map (consˣ outside) (monomials≤ n m (suc d))) g)
  (cong₂ _+ℤ_
    (trans (Σˡ-map (consˣ inside) (monomials≤ n m d) g)
      (trans (Σˡ-monomials≤ n m d (λ γ → g (consˣ inside γ)))
             (Σmon-cong (λ γ →
               sym (cut-suc d ∥ γ ∥ (g (consˣ inside γ)))))))
    (trans (Σˡ-map (consˣ outside) (monomials≤ n m (suc d)) g)
           (Σˡ-monomials≤ n m (suc d) (λ γ → g (consˣ outside γ)))))

-- So the listing has one entry per monomial of degree at most d.

length-monomials≤-exact : ∀ n m d →
  + length (monomials≤ n m d) ≡ Σmon {n} {m} (λ γ → cut d ∥ γ ∥ 1ℤ)
length-monomials≤-exact n m d =
  trans (sym (Σˡ-1 (monomials≤ n m d))) (Σˡ-monomials≤ n m d (λ _ → 1ℤ))


------------------------------------------------------------------------
-- The counting lemma

-- The bound survives Pascal's rule.

pascal-≤ : ∀ a d → a ^ d + a ^ suc d ≤ suc a ^ suc d
pascal-≤ a d = ℕ.+-mono-≤ a^d≤ (ℕ.*-monoʳ-≤ a a^d≤)
  where
  a^d≤ : a ^ d ≤ suc a ^ d
  a^d≤ = ℕ.^-monoˡ-≤ d (ℕ.n≤1+n a)

length-subsets≤ : ∀ k d → length (subsets≤ k d) ≤ suc k ^ d
length-subsets≤ zero    d       = ℕ.≤-reflexive (sym (ℕ.^-zeroˡ d))
length-subsets≤ (suc k) zero    = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (outside ∷_) (subsets≤ k zero)))
  (length-subsets≤ k zero)
length-subsets≤ (suc k) (suc d) = ℕ.≤-trans
  (ℕ.≤-reflexive (trans
    (List.length-++ (map (inside ∷_) (subsets≤ k d)))
    (cong₂ _+_ (List.length-map (inside ∷_) (subsets≤ k d))
               (List.length-map (outside ∷_) (subsets≤ k (suc d))))))
  (ℕ.≤-trans (ℕ.+-mono-≤ (length-subsets≤ k d)
                         (length-subsets≤ k (suc d)))
             (pascal-≤ (suc k) d))

-- At most (n + m + 1)^d monomials of degree at most d.

length-monomials≤ : ∀ n m d → length (monomials≤ n m d) ≤ suc (n + m) ^ d
length-monomials≤ zero    m d       = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (λ β → [] , β) (subsets≤ m d)))
  (length-subsets≤ m d)
length-monomials≤ (suc n) m zero    = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (consˣ outside) (monomials≤ n m zero)))
  (length-monomials≤ n m zero)
length-monomials≤ (suc n) m (suc d) = ℕ.≤-trans
  (ℕ.≤-reflexive (trans
    (List.length-++ (map (consˣ inside) (monomials≤ n m d)))
    (cong₂ _+_
      (List.length-map (consˣ inside) (monomials≤ n m d))
      (List.length-map (consˣ outside) (monomials≤ n m (suc d))))))
  (ℕ.≤-trans (ℕ.+-mono-≤ (length-monomials≤ n m d)
                         (length-monomials≤ n m (suc d)))
             (pascal-≤ (suc (n + m)) d))


------------------------------------------------------------------------
-- The exact count

-- Σ_{i ≤ d} f i, and the number of subsets of size at most d of a set
-- of k elements, Σ_{i ≤ d} C(k, i).

Σ≤ : (ℕ → ℕ) → ℕ → ℕ
Σ≤ f zero    = f zero
Σ≤ f (suc d) = Σ≤ f d + f (suc d)

binomials : ℕ → ℕ → ℕ
binomials k d = Σ≤ (λ i → k C i) d

-- Pascal's rule, summed.

private
  binomials-0 : ∀ d → binomials 0 d ≡ 1
  binomials-0 zero    = refl
  binomials-0 (suc d) =
    trans (ℕ.+-identityʳ (binomials 0 d)) (binomials-0 d)

  medial : ∀ a b c e → (a + b) + (c + e) ≡ (a + c) + (b + e)
  medial = solve 4 (λ a b c e → (a :+ b) :+ (c :+ e) := (a :+ c) :+ (b :+ e))
                   refl
    where open +-*-Solver using (solve; _:+_; _:=_)

pascal-binomials : ∀ k d →
  binomials (suc k) (suc d) ≡ binomials k d + binomials k (suc d)
pascal-binomials k zero    =
  cong suc (sym (nCk+nC[k+1]≡[n+1]C[k+1] k 0))
pascal-binomials k (suc d) = trans
  (cong₂ _+_ (pascal-binomials k d)
             (sym (nCk+nC[k+1]≡[n+1]C[k+1] k (suc d))))
  (medial (binomials k d) (binomials k (suc d))
          (k C suc d) (k C suc (suc d)))

-- The listing has exactly that many entries.

length-subsets≤-binomial : ∀ k d → length (subsets≤ k d) ≡ binomials k d
length-subsets≤-binomial zero    d       = sym (binomials-0 d)
length-subsets≤-binomial (suc k) zero    = trans
  (List.length-map (outside ∷_) (subsets≤ k zero))
  (length-subsets≤-binomial k zero)
length-subsets≤-binomial (suc k) (suc d) = trans
  (List.length-++ (map (inside ∷_) (subsets≤ k d)))
  (trans (cong₂ _+_
           (trans (List.length-map (inside ∷_) (subsets≤ k d))
                  (length-subsets≤-binomial k d))
           (trans (List.length-map (outside ∷_) (subsets≤ k (suc d)))
                  (length-subsets≤-binomial k (suc d))))
         (sym (pascal-binomials k d)))

length-monomials≤-binomial : ∀ n m d →
  length (monomials≤ n m d) ≡ binomials (n + m) d
length-monomials≤-binomial zero    m d       = trans
  (List.length-map (λ β → [] , β) (subsets≤ m d))
  (length-subsets≤-binomial m d)
length-monomials≤-binomial (suc n) m zero    = trans
  (List.length-map (consˣ outside) (monomials≤ n m zero))
  (length-monomials≤-binomial n m zero)
length-monomials≤-binomial (suc n) m (suc d) = trans
  (List.length-++ (map (consˣ inside) (monomials≤ n m d)))
  (trans (cong₂ _+_
           (trans (List.length-map (consˣ inside) (monomials≤ n m d))
                  (length-monomials≤-binomial n m d))
           (trans (List.length-map (consˣ outside) (monomials≤ n m (suc d)))
                  (length-monomials≤-binomial n m (suc d))))
         (sym (pascal-binomials (n + m) d)))
