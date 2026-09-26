------------------------------------------------------------------------
-- Presentations of groups
--
-- The submonomials of bounded degree of a monomial, listed and counted
-- (for Amy, QPL 2018, lemma 2.13 and corollary 2.15)
--
-- The proof of lemma 2.13 expands a parity as
--
--    ⨁_{j ∈ S} x_j = Σ_{∅ ≠ S′ ⊆ S} (-2)^(|S′|-1) Π_{j ∈ S′} x_j ,
--
-- so the terms of the lifting of a Z₂-linear form c ⊕ ⨁S are indexed
-- by the subsets of S: the submonomials of the monomial S.  The sparse
-- interpreter of PathSum.Size.Interpreter (whose header has the plan
-- of this part of the development) writes down those of degree at
-- most d, and subᵐ≤ α β d lists them, by Pascal's rule on the
-- variables of S = (α , β), as PathSum.Size.Monomials.monomials≤ does
-- on all the variables.  Proved here:
--
--  * summing over the list is summing over all monomials, cut off
--    outside S and above degree d (Σˡ-subᵐ≤), so each submonomial of
--    degree at most d is listed exactly once and nothing else is;
--  * each entry has degree at most d (subᵐ≤-small);
--  * there are exactly Σ_{i ≤ d} C(|S|, i) of them
--    (length-subᵐ≤-binomial), hence at most (|S| + 1)^d
--    (length-subᵐ≤).
--
-- subsOf≤ is the same for a single subset.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Size.Submonomials where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Subset using (Subset; inside; outside; ∣_∣)
open import Data.Integer.Base using (ℤ; 0ℤ)
  renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _^_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Polynomial using (Mon; ∥_∥; Σsub; Σmon)
open import PathSum.Polynomial.Properties using
  (_⊆ᵇ_; _⊆ᵐᵇ_; Σsub-0; Σsub-cong; Σmon-0; Σmon-cong)
open import PathSum.Size.Monomials using
  (Σˡ; Σˡ-++; Σˡ-map; cut; cut-suc; consˣ; pascal-≤; binomials;
   pascal-binomials; subsets≤; length-subsets≤-binomial)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- The listings

-- The subsets of p of size at most d, by Pascal's rule on the head.

subsOf≤ : Subset k → ℕ → List (Subset k)
subsOf≤ []            d       = [] ∷ []
subsOf≤ (outside ∷ p) d       = map (outside ∷_) (subsOf≤ p d)
subsOf≤ (inside  ∷ p) zero    = map (outside ∷_) (subsOf≤ p zero)
subsOf≤ (inside  ∷ p) (suc d) =
  map (inside ∷_) (subsOf≤ p d) ++ map (outside ∷_) (subsOf≤ p (suc d))

-- The submonomials of (α , β) of degree at most d: Pascal's rule on
-- α, then on β.

subᵐ≤ : Subset n → Subset m → ℕ → List (Mon n m)
subᵐ≤ []            β d       = map (λ b → [] , b) (subsOf≤ β d)
subᵐ≤ (outside ∷ α) β d       = map (consˣ outside) (subᵐ≤ α β d)
subᵐ≤ (inside  ∷ α) β zero    = map (consˣ outside) (subᵐ≤ α β zero)
subᵐ≤ (inside  ∷ α) β (suc d) =
  map (consˣ inside) (subᵐ≤ α β d) ++
  map (consˣ outside) (subᵐ≤ α β (suc d))


------------------------------------------------------------------------
-- Every submonomial of degree at most d, exactly once

private
  if-0 : ∀ (b : Bool) → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0 true  = refl
  if-0 false = refl

Σˡ-subsOf≤ : ∀ (p : Subset k) d (g : Subset k → ℤ) →
             Σˡ (subsOf≤ p d) g ≡
             Σsub (λ s → if s ⊆ᵇ p then cut d ∣ s ∣ (g s) else 0ℤ)
Σˡ-subsOf≤ []            d       g = ℤP.+-identityʳ (g [])
Σˡ-subsOf≤ {suc k} (outside ∷ p) d g = trans
  (Σˡ-map (outside ∷_) (subsOf≤ p d) g)
  (trans (Σˡ-subsOf≤ p d (λ s → g (outside ∷ s)))
         (sym (trans (cong (_+ℤ rest) (Σsub-0 {k}))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σsub (λ s → if s ⊆ᵇ p then cut d ∣ s ∣ (g (outside ∷ s)) else 0ℤ)
Σˡ-subsOf≤ {suc k} (inside ∷ p) zero g = trans
  (Σˡ-map (outside ∷_) (subsOf≤ p zero) g)
  (trans (Σˡ-subsOf≤ p zero (λ s → g (outside ∷ s)))
         (sym (trans (cong (_+ℤ rest)
                       (trans (Σsub-cong (λ s → if-0 (s ⊆ᵇ p)))
                              (Σsub-0 {k})))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σsub (λ s → if s ⊆ᵇ p then cut zero ∣ s ∣ (g (outside ∷ s))
                     else 0ℤ)
Σˡ-subsOf≤ (inside ∷ p) (suc d) g = trans
  (Σˡ-++ (map (inside ∷_) (subsOf≤ p d))
         (map (outside ∷_) (subsOf≤ p (suc d))) g)
  (cong₂ _+ℤ_
    (trans (Σˡ-map (inside ∷_) (subsOf≤ p d) g)
      (trans (Σˡ-subsOf≤ p d (λ s → g (inside ∷ s)))
             (Σsub-cong (λ s → cong (λ z → if s ⊆ᵇ p then z else 0ℤ)
                          (sym (cut-suc d ∣ s ∣ (g (inside ∷ s))))))))
    (trans (Σˡ-map (outside ∷_) (subsOf≤ p (suc d)) g)
           (Σˡ-subsOf≤ p (suc d) (λ s → g (outside ∷ s)))))

Σˡ-subᵐ≤ : ∀ (α : Subset n) (β : Subset m) d (g : Mon n m → ℤ) →
           Σˡ (subᵐ≤ α β d) g ≡
           Σmon (λ γ → if γ ⊆ᵐᵇ (α , β) then cut d ∥ γ ∥ (g γ) else 0ℤ)
Σˡ-subᵐ≤ []            β d       g = trans
  (Σˡ-map (λ b → [] , b) (subsOf≤ β d) g)
  (Σˡ-subsOf≤ β d (λ b → g ([] , b)))
Σˡ-subᵐ≤ {suc n} {m} (outside ∷ α) β d g = trans
  (Σˡ-map (consˣ outside) (subᵐ≤ α β d) g)
  (trans (Σˡ-subᵐ≤ α β d (λ γ → g (consˣ outside γ)))
         (sym (trans (cong (_+ℤ rest) (Σmon-0 {n} {m}))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σmon (λ γ → if γ ⊆ᵐᵇ (α , β)
                     then cut d ∥ γ ∥ (g (consˣ outside γ)) else 0ℤ)
Σˡ-subᵐ≤ {suc n} {m} (inside ∷ α) β zero g = trans
  (Σˡ-map (consˣ outside) (subᵐ≤ α β zero) g)
  (trans (Σˡ-subᵐ≤ α β zero (λ γ → g (consˣ outside γ)))
         (sym (trans (cong (_+ℤ rest)
                       (trans (Σmon-cong (λ γ → if-0 (γ ⊆ᵐᵇ (α , β))))
                              (Σmon-0 {n} {m})))
                     (ℤP.+-identityˡ rest))))
  where
  rest : ℤ
  rest = Σmon (λ γ → if γ ⊆ᵐᵇ (α , β)
                     then cut zero ∥ γ ∥ (g (consˣ outside γ)) else 0ℤ)
Σˡ-subᵐ≤ (inside ∷ α) β (suc d) g = trans
  (Σˡ-++ (map (consˣ inside) (subᵐ≤ α β d))
         (map (consˣ outside) (subᵐ≤ α β (suc d))) g)
  (cong₂ _+ℤ_
    (trans (Σˡ-map (consˣ inside) (subᵐ≤ α β d) g)
      (trans (Σˡ-subᵐ≤ α β d (λ γ → g (consˣ inside γ)))
             (Σmon-cong (λ γ → cong (λ z → if γ ⊆ᵐᵇ (α , β) then z else 0ℤ)
               (sym (cut-suc d ∥ γ ∥ (g (consˣ inside γ))))))))
    (trans (Σˡ-map (consˣ outside) (subᵐ≤ α β (suc d)) g)
           (Σˡ-subᵐ≤ α β (suc d) (λ γ → g (consˣ outside γ)))))


------------------------------------------------------------------------
-- Every entry has degree at most d

subsOf≤-small : ∀ (p : Subset k) d → All (λ s → ∣ s ∣ ≤ d) (subsOf≤ p d)
subsOf≤-small []            d       = z≤n ∷ []
subsOf≤-small (outside ∷ p) d       =
  AllP.map⁺ {f = outside ∷_} (subsOf≤-small p d)
subsOf≤-small (inside  ∷ p) zero    =
  AllP.map⁺ {f = outside ∷_} (subsOf≤-small p zero)
subsOf≤-small (inside  ∷ p) (suc d) = AllP.++⁺
  (AllP.map⁺ {f = inside ∷_} (All.map s≤s (subsOf≤-small p d)))
  (AllP.map⁺ {f = outside ∷_} (subsOf≤-small p (suc d)))

subᵐ≤-small : ∀ (α : Subset n) (β : Subset m) d →
              All (λ γ → ∥ γ ∥ ≤ d) (subᵐ≤ α β d)
subᵐ≤-small []            β d       =
  AllP.map⁺ {f = λ b → [] , b} (subsOf≤-small β d)
subᵐ≤-small (outside ∷ α) β d       =
  AllP.map⁺ {f = consˣ outside} (subᵐ≤-small α β d)
subᵐ≤-small (inside  ∷ α) β zero    =
  AllP.map⁺ {f = consˣ outside} (subᵐ≤-small α β zero)
subᵐ≤-small (inside  ∷ α) β (suc d) = AllP.++⁺
  (AllP.map⁺ {f = consˣ inside} (All.map s≤s (subᵐ≤-small α β d)))
  (AllP.map⁺ {f = consˣ outside} (subᵐ≤-small α β (suc d)))


------------------------------------------------------------------------
-- The count

-- Exactly Σ_{i ≤ d} C(|S|, i) entries: Pascal's rule for the binomial
-- coefficients.

private
  length-++-map : ∀ {A B : Set} (f g : A → B) (as bs : List A) →
                  length (map f as ++ map g bs) ≡ length as + length bs
  length-++-map f g as bs = trans (List.length-++ (map f as))
    (cong₂ _+_ (List.length-map f as) (List.length-map g bs))

length-subsOf≤-binomial : ∀ (p : Subset k) d →
                          length (subsOf≤ p d) ≡ binomials ∣ p ∣ d
length-subsOf≤-binomial []            d       =
  length-subsets≤-binomial 0 d
length-subsOf≤-binomial (outside ∷ p) d       = trans
  (List.length-map (outside ∷_) (subsOf≤ p d))
  (length-subsOf≤-binomial p d)
length-subsOf≤-binomial (inside  ∷ p) zero    = trans
  (List.length-map (outside ∷_) (subsOf≤ p zero))
  (length-subsOf≤-binomial p zero)
length-subsOf≤-binomial (inside  ∷ p) (suc d) = trans
  (length-++-map (inside ∷_) (outside ∷_) (subsOf≤ p d)
                 (subsOf≤ p (suc d)))
  (trans (cong₂ _+_ (length-subsOf≤-binomial p d)
                    (length-subsOf≤-binomial p (suc d)))
         (sym (pascal-binomials ∣ p ∣ d)))

length-subᵐ≤-binomial : ∀ (α : Subset n) (β : Subset m) d →
  length (subᵐ≤ α β d) ≡ binomials ∥ (α , β) ∥ d
length-subᵐ≤-binomial []            β d       = trans
  (List.length-map (λ b → [] , b) (subsOf≤ β d))
  (length-subsOf≤-binomial β d)
length-subᵐ≤-binomial (outside ∷ α) β d       = trans
  (List.length-map (consˣ outside) (subᵐ≤ α β d))
  (length-subᵐ≤-binomial α β d)
length-subᵐ≤-binomial (inside  ∷ α) β zero    = trans
  (List.length-map (consˣ outside) (subᵐ≤ α β zero))
  (length-subᵐ≤-binomial α β zero)
length-subᵐ≤-binomial (inside  ∷ α) β (suc d) = trans
  (length-++-map (consˣ inside) (consˣ outside) (subᵐ≤ α β d)
                 (subᵐ≤ α β (suc d)))
  (trans (cong₂ _+_ (length-subᵐ≤-binomial α β d)
                    (length-subᵐ≤-binomial α β (suc d)))
         (sym (pascal-binomials ∥ (α , β) ∥ d)))

-- Hence at most (|S| + 1)^d: the bound survives Pascal's rule.

length-subsOf≤ : ∀ (p : Subset k) d → length (subsOf≤ p d) ≤ suc ∣ p ∣ ^ d
length-subsOf≤ []            d       = ℕ.≤-reflexive (sym (ℕ.^-zeroˡ d))
length-subsOf≤ (outside ∷ p) d       = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (outside ∷_) (subsOf≤ p d)))
  (length-subsOf≤ p d)
length-subsOf≤ (inside  ∷ p) zero    = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (outside ∷_) (subsOf≤ p zero)))
  (length-subsOf≤ p zero)
length-subsOf≤ (inside  ∷ p) (suc d) = ℕ.≤-trans
  (ℕ.≤-reflexive (length-++-map (inside ∷_) (outside ∷_) (subsOf≤ p d)
                                (subsOf≤ p (suc d))))
  (ℕ.≤-trans (ℕ.+-mono-≤ (length-subsOf≤ p d) (length-subsOf≤ p (suc d)))
             (pascal-≤ (suc ∣ p ∣) d))

length-subᵐ≤ : ∀ (α : Subset n) (β : Subset m) d →
               length (subᵐ≤ α β d) ≤ suc ∥ (α , β) ∥ ^ d
length-subᵐ≤ []            β d       = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (λ b → [] , b) (subsOf≤ β d)))
  (length-subsOf≤ β d)
length-subᵐ≤ (outside ∷ α) β d       = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (consˣ outside) (subᵐ≤ α β d)))
  (length-subᵐ≤ α β d)
length-subᵐ≤ (inside  ∷ α) β zero    = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-map (consˣ outside) (subᵐ≤ α β zero)))
  (length-subᵐ≤ α β zero)
length-subᵐ≤ (inside  ∷ α) β (suc d) = ℕ.≤-trans
  (ℕ.≤-reflexive (length-++-map (consˣ inside) (consˣ outside)
                                (subᵐ≤ α β d) (subᵐ≤ α β (suc d))))
  (ℕ.≤-trans (ℕ.+-mono-≤ (length-subᵐ≤ α β d) (length-subᵐ≤ α β (suc d)))
             (pascal-≤ (suc ∥ (α , β) ∥) d))
