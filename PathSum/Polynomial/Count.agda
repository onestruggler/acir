------------------------------------------------------------------------
-- Presentations of groups
--
-- Counting monomials, and polynomials written as lists of terms
--
-- A polynomial in this development is a function on all monomials
-- (PathSum.Polynomial.Poly), so "the number of terms of a polynomial"
-- is not a property of a Poly value: it is the number of monomials on
-- which the coefficient is non-zero, or, for a Boolean polynomial read
-- modulo 2 as outputs are, odd.  This module supplies both readings.
--
-- * count p is the number of subsets s of k variables -- the
--   monomials in those variables -- with p s true, the sum over all
--   2^k of them in the order of PathSum.Polynomial's Σsub.  The usual
--   facts: it only reads the values of p (count-cong), is monotone
--   (count-mono), counts at most 1 for a predicate true at most once
--   (count-≤1), 0 for nothing (count-none) and 2^k for everything
--   (count-true).
--
-- * A polynomial written down as a list of terms (a , c), standing for
--   Σ c · x^a (⟦_⟧ᵗ, over any type of monomials with decidable
--   equality), has a non-zero, in particular an odd, coefficient only
--   on monomials it lists (listed).  So if an injective family g of
--   monomials, indexed by the subsets s with p s, all have odd
--   coefficients, the list has at least count p terms (count-cover).
--   That is how a lower bound on the number of odd coefficients
--   becomes a lower bound on the length of every representation that
--   lists its terms, whatever their order and whatever repetitions or
--   terms with even coefficients it contains.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Count where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ) renaming (_+_ to _+ℤ_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (+-mono-≤; ≤-trans; ≤-reflexive; ≤-refl; +-comm; +-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; ∃)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Bool.Properties as Bool
import Data.Vec.Properties as Vec

open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Parity using (odd-0)

open +-*-Solver using (solve; _:+_; _:=_)

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- Counting subsets

-- The number of monomials in k variables on which p holds.

count : (Subset k → Bool) → ℕ
count {zero}  p = if p [] then 1 else 0
count {suc k} p = count (λ s → p (inside ∷ s)) + count (λ s → p (outside ∷ s))

-- It reads p through its values.

count-cong : {p q : Subset k → Bool} → (∀ s → p s ≡ q s) → count p ≡ count q
count-cong {zero}  h = cong (λ b → if b then 1 else 0) (h [])
count-cong {suc k} h = cong₂ _+_ (count-cong (λ s → h (inside ∷ s)))
                                 (count-cong (λ s → h (outside ∷ s)))

-- Nothing counts 0, everything 2^k.

count-false : count {k} (λ _ → false) ≡ 0
count-false {zero}  = refl
count-false {suc k} = cong₂ _+_ (count-false {k}) (count-false {k})

count-true : count {k} (λ _ → true) ≡ 2 ^ k
count-true {zero}  = refl
count-true {suc k} = trans (cong₂ _+_ (count-true {k}) (count-true {k}))
                           (cong (2 ^ k +_) (sym (+-identityʳ (2 ^ k))))

private
  false-if-not-true : ∀ {b} → ¬ (b ≡ true) → b ≡ false
  false-if-not-true {false} _ = refl
  false-if-not-true {true}  h = contradiction refl h

count-none : (p : Subset k → Bool) → (∀ s → ¬ (p s ≡ true)) → count p ≡ 0
count-none {k} p h =
  trans (count-cong (λ s → false-if-not-true (h s))) (count-false {k})

-- Monotone.

count-mono : (p q : Subset k → Bool) → (∀ s → p s ≡ true → q s ≡ true) →
             count p ≤ count q
count-mono {zero}  p q h = base (p []) (q []) (h [])
  where
  base : ∀ a b → (a ≡ true → b ≡ true) →
         (if a then 1 else 0) ≤ (if b then 1 else 0)
  base false b     _ = z≤n
  base true  true  _ = ≤-refl
  base true  false i with i refl
  ... | ()
count-mono {suc k} p q h = +-mono-≤
  (count-mono (λ s → p (inside ∷ s)) (λ s → q (inside ∷ s))
              (λ s → h (inside ∷ s)))
  (count-mono (λ s → p (outside ∷ s)) (λ s → q (outside ∷ s))
              (λ s → h (outside ∷ s)))

-- A predicate that holds somewhere, holds somewhere in particular.

count-witness : ∀ {c} (p : Subset k → Bool) → count p ≡ suc c →
                ∃ λ s → p s ≡ true
count-witness {zero} {c} p eq = go (p []) refl eq
  where
  go : ∀ b → p [] ≡ b → (if b then 1 else 0) ≡ suc c → ∃ λ s → p s ≡ true
  go true  e _ = [] , e
  go false e ()
count-witness {suc k} {c} p eq = go (count p₁) refl
  where
  p₁ p₀ : Subset k → Bool
  p₁ s = p (inside ∷ s)
  p₀ s = p (outside ∷ s)

  go : ∀ d → count p₁ ≡ d → ∃ λ s → p s ≡ true
  go zero    e with count-witness p₀
                      (trans (sym (cong (_+ count p₀) e)) eq)
  ... | s , ps = outside ∷ s , ps
  go (suc d) e with count-witness p₁ e
  ... | s , ps = inside ∷ s , ps

-- A predicate that holds at most once counts at most 1.

private
  ∷-injectiveʳ : ∀ {a b} {s t : Subset k} → (a ∷ s) ≡ (b ∷ t) → s ≡ t
  ∷-injectiveʳ refl = refl

  inside≢outside : {s t : Subset k} → ¬ ((inside ∷ s) ≡ (outside ∷ t))
  inside≢outside ()

count-≤1 : (p : Subset k → Bool) →
           (∀ s t → p s ≡ true → p t ≡ true → s ≡ t) → count p ≤ 1
count-≤1 {zero}  p u with p []
... | true  = ≤-refl
... | false = z≤n
count-≤1 {suc k} p u = go (count p₁) refl
  where
  p₁ p₀ : Subset k → Bool
  p₁ s = p (inside ∷ s)
  p₀ s = p (outside ∷ s)

  u₁ : ∀ s t → p₁ s ≡ true → p₁ t ≡ true → s ≡ t
  u₁ s t hs ht = ∷-injectiveʳ (u (inside ∷ s) (inside ∷ t) hs ht)

  u₀ : ∀ s t → p₀ s ≡ true → p₀ t ≡ true → s ≡ t
  u₀ s t hs ht = ∷-injectiveʳ (u (outside ∷ s) (outside ∷ t) hs ht)

  go : ∀ d → count p₁ ≡ d → count p₁ + count p₀ ≤ 1
  go zero    e = subst (λ c → c + count p₀ ≤ 1) (sym e) (count-≤1 p₀ u₀)
  go (suc d) e with count-witness p₁ e
  ... | s₁ , h₁ = subst (_≤ 1)
          (sym (trans (cong (count p₁ +_) none₀) (+-identityʳ (count p₁))))
          (count-≤1 p₁ u₁)
    where
    none₀ : count p₀ ≡ 0
    none₀ = count-none p₀
      (λ t h₀ → inside≢outside (u (inside ∷ s₁) (outside ∷ t) h₁ h₀))

-- Taking a predicate out of p costs at most its own count.

count-split : (p e : Subset k → Bool) →
              count p ≤ count (λ s → p s ∧ not (e s)) + count e
count-split {zero}  p e = base (p []) (e [])
  where
  base : ∀ a b → (if a then 1 else 0) ≤
                 (if a ∧ not b then 1 else 0) + (if b then 1 else 0)
  base false false = z≤n
  base false true  = z≤n
  base true  false = ≤-refl
  base true  true  = ≤-refl
count-split {suc k} p e = ≤-trans
  (+-mono-≤ (count-split p₁ e₁) (count-split p₀ e₀))
  (≤-reflexive (shuffle (count (λ s → p₁ s ∧ not (e₁ s))) (count e₁)
                        (count (λ s → p₀ s ∧ not (e₀ s))) (count e₀)))
  where
  p₁ p₀ e₁ e₀ : Subset k → Bool
  p₁ s = p (inside ∷ s)
  p₀ s = p (outside ∷ s)
  e₁ s = e (inside ∷ s)
  e₀ s = e (outside ∷ s)

  shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d))
                    refl


------------------------------------------------------------------------
-- Lists covering an injective family

module _ {A : Set} (_≟_ : DecidableEquality A) where

  private
    -- Reading a decided equality back.

    ⌊≟⌋-true : ∀ a b → ⌊ a ≟ b ⌋ ≡ true → a ≡ b
    ⌊≟⌋-true a b h with a ≟ b
    ... | yes e = e
    ... | no  _ = contradiction h λ ()

    ⌊≟⌋-false : ∀ a b → ⌊ a ≟ b ⌋ ≡ false → ¬ (a ≡ b)
    ⌊≟⌋-false a b h e with a ≟ b
    ... | yes _  = contradiction h λ ()
    ... | no  ¬e = ¬e e

    ∧-true : ∀ {a b} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
    ∧-true {true}  {true}  _  = refl , refl
    ∧-true {true}  {false} ()
    ∧-true {false}         ()

    not-true : ∀ {b} → not b ≡ true → b ≡ false
    not-true {false} _  = refl
    not-true {true}  ()

  -- If every member of an injective family g indexed by the subsets on
  -- which p holds is in the list L, L has at least count p entries.

  count-cover : (p : Subset k → Bool) (g : Subset k → A) →
                (∀ s t → g s ≡ g t → s ≡ t) → (L : List A) →
                (∀ s → p s ≡ true → g s ∈ L) → count p ≤ length L
  count-cover p g inj []      cov =
    ≤-reflexive (count-none p (λ s h → absurd (cov s h)))
    where
    absurd : ∀ {a} → ¬ (a ∈ [])
    absurd ()
  count-cover {k} p g inj (a ∷ L) cov = ≤-trans
    (count-split p e)
    (≤-trans (+-mono-≤ (count-cover p′ g inj L cov′) (count-≤1 e unique))
             (≤-reflexive (+-comm (length L) 1)))
    where
    e p′ : Subset k → Bool
    e s  = ⌊ g s ≟ a ⌋
    p′ s = p s ∧ not (e s)

    cov′ : ∀ s → p′ s ≡ true → g s ∈ L
    cov′ s h with ∧-true {p s} {not (e s)} h
    ... | ps , ne with cov s ps
    ...   | here  g≡a = contradiction g≡a (⌊≟⌋-false (g s) a (not-true ne))
    ...   | there g∈L = g∈L

    unique : ∀ s t → e s ≡ true → e t ≡ true → s ≡ t
    unique s t hs ht =
      inj s t (trans (⌊≟⌋-true (g s) a hs) (sym (⌊≟⌋-true (g t) a ht)))


------------------------------------------------------------------------
-- Polynomials as lists of terms

module Terms {A : Set} (_≟_ : DecidableEquality A) where

  -- The list of terms (a , c) stands for Σ c · x^a: its coefficient on
  -- a monomial collects the terms listing it.

  ⟦_⟧ᵗ : List (A × ℤ) → A → ℤ
  ⟦ []          ⟧ᵗ a = 0ℤ
  ⟦ (b , c) ∷ ts ⟧ᵗ a = (if ⌊ a ≟ b ⌋ then c else 0ℤ) +ℤ ⟦ ts ⟧ᵗ a

  -- A monomial with an odd coefficient is listed.

  listed : (ts : List (A × ℤ)) (a : A) → odd (⟦ ts ⟧ᵗ a) ≡ true →
           a ∈ map proj₁ ts
  listed []             a h = contradiction (trans (sym h) odd-0) λ ()
  listed ((b , c) ∷ ts) a h with a ≟ b
  ... | yes a≡b = here a≡b
  ... | no  _   = there (listed ts a (trans (cong odd (sym (+-identityˡ _))) h))

  -- So a list in which an injective family of count p monomials all
  -- have odd coefficients has at least count p terms.

  terms-cover : (p : Subset k → Bool) (g : Subset k → A) →
                (∀ s t → g s ≡ g t → s ≡ t) → (ts : List (A × ℤ)) →
                (∀ s → p s ≡ true → odd (⟦ ts ⟧ᵗ (g s)) ≡ true) →
                count p ≤ length ts
  terms-cover p g inj ts h = subst (count p ≤_) (length-map ts)
    (count-cover _≟_ p g inj (map proj₁ ts)
                 (λ s ps → listed ts (g s) (h s ps)))
    where
    length-map : (ts : List (A × ℤ)) → length (map proj₁ ts) ≡ length ts
    length-map []       = refl
    length-map (_ ∷ ts) = cong suc (length-map ts)

-- Monomials in k variables have decidable equality.

_≟ˢ_ : DecidableEquality (Subset k)
_≟ˢ_ = Vec.≡-dec Bool._≟_
