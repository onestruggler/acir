------------------------------------------------------------------------
-- Presentations of groups
--
-- The order of a phase polynomial (Amy, QPL 2018, definition 2.11),
-- and the fact that order does not increase under substitution of a
-- linear Boolean polynomial (lemma 2.13)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Order (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_; _-_)
  renaming (_+_ to _+ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣-refl; ∣-trans; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣n⇒∣m*n;
   *-monoʳ-∣; *-monoˡ-∣)
open import Data.Integer.DivMod using (_/_; _%_; n%d<d; a≡a%n+[a/n]*n)
open import Data.Integer.Properties using
  (pos-*; +-identityˡ; +-comm; *-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using
  (zero; suc; _+_; _∸_; _^_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Polynomial
open import PathSum.Polynomial.Properties

import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; _:+_; _:-_; _:*_; _:=_)

private
  variable
    d n m : ℕ


------------------------------------------------------------------------
-- The order of a polynomial

-- 2 ^ e, as an integer.

pow : ℕ → ℤ
pow e = + (2 ^ e)

-- The 2-adic valuation demanded of the coefficient of a monomial of
-- degree s in a polynomial of order at most d.  A term (a/2^b) x^α
-- with a odd has order b + |α| - 1, so ord (P) ≤ d asks for
-- b ≤ d + 1 - |α|, that is, for the numerator over 2^M of the
-- coefficient to be divisible by 2^(M - (d + 1 - |α|)).

val : ℕ → ℕ → ℕ
val d s = M ∸ (suc d ∸ s)

-- Definition 2.11.

Ord≤ : ℕ → Poly n m → Set
Ord≤ d P = ∀ γ → pow (val d ∥ γ ∥) ∣ P γ


------------------------------------------------------------------------
-- Arithmetic of the valuation

val≤M : ∀ d s → val d s ≤ M
val≤M d s = ℕ.m∸n≤m M (suc d ∸ s)

val-mono : ∀ d {s t} → s ≤ t → val d s ≤ val d t
val-mono d s≤t = ℕ.∸-monoʳ-≤ M (ℕ.∸-monoʳ-≤ (suc d) s≤t)

private
  n≤suc[n∸1] : ∀ i → i ≤ suc (i ∸ 1)
  n≤suc[n∸1] zero    = z≤n
  n≤suc[n∸1] (suc i) = ℕ.≤-refl

  ∸-∸-≤ : ∀ i u t → i ∸ (u ∸ t) ≤ (i ∸ u) + t
  ∸-∸-≤ i u zero = ℕ.≤-reflexive (sym (ℕ.+-identityʳ (i ∸ u)))
  ∸-∸-≤ i zero (suc t) = ℕ.m≤m+n i (suc t)
  ∸-∸-≤ i (suc u) (suc t) = ℕ.≤-trans (∸-∸-≤ i u t) (ℕ.≤-trans
    (ℕ.+-monoˡ-≤ t step)
    (ℕ.≤-reflexive (sym (ℕ.+-suc (i ∸ suc u) t))))
    where
    step : (i ∸ u) ≤ suc (i ∸ suc u)
    step = ℕ.≤-trans (n≤suc[n∸1] (i ∸ u)) (s≤s (ℕ.≤-reflexive
      (trans (ℕ.∸-+-assoc i u 1) (cong (i ∸_) (ℕ.+-comm u 1)))))

-- The valuation grows by at most one per unit of degree.

val-step : ∀ d s t → val d (s + suc t) ≤ val d (suc s) + t
val-step d s t = ℕ.≤-trans
  (ℕ.≤-reflexive (cong (M ∸_) shuffle))
  (∸-∸-≤ M (suc d ∸ suc s) t)
  where
  shuffle : suc d ∸ (s + suc t) ≡ (suc d ∸ suc s) ∸ t
  shuffle = trans (cong (suc d ∸_) (ℕ.+-suc s t))
                  (sym (ℕ.∸-+-assoc (suc d) (suc s) t))

-- The bound needed for a term of degree |δ| + 1 substituted into a
-- monomial of degree at most |δ| + |β|.

val-bound : ∀ d s b g → g ≤ s + b → val d g ≤ val d (suc s) + (b ∸ 1)
val-bound d s zero g g≤ = ℕ.≤-trans
  (val-mono d (ℕ.≤-trans g≤
    (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ s)) (ℕ.n≤1+n s))))
  (ℕ.≤-reflexive (sym (ℕ.+-identityʳ (val d (suc s)))))
val-bound d s (suc t) g g≤ =
  ℕ.≤-trans (val-mono d g≤) (val-step d s t)

pow-∣ : ∀ {a b} → a ≤ b → pow a ∣ pow b
pow-∣ = 2^-mono-∣

pow-+ : ∀ a b → pow a * pow b ≡ pow (a + b)
pow-+ a b = trans (sym (pos-* (2 ^ a) (2 ^ b)))
                  (cong +_ (sym (ℕ.^-distribˡ-+-* 2 a b)))


------------------------------------------------------------------------
-- Extracting a dyadic digit

pow-suc : ∀ e → pow (suc e) ≡ pow e * (+ 2)
pow-suc e = trans (cong +_ (ℕ.*-comm 2 (2 ^ e))) (pos-* (2 ^ e) 2)

-- Every integer is even or odd.

parity : ∀ q → (∃ λ r → q ≡ r * (+ 2)) ⊎ (∃ λ r → q ≡ (r * (+ 2)) +ℤ 1ℤ)
parity q with q % (+ 2) in eqr | n%d<d q (+ 2)
... | zero        | _ = inj₁ (q / (+ 2) , trans (trans expand digit≡) (+-identityˡ _))
  where
  expand : q ≡ (+ (q % (+ 2))) +ℤ ((q / (+ 2)) * (+ 2))
  expand = a≡a%n+[a/n]*n q (+ 2)

  digit≡ : (+ (q % (+ 2))) +ℤ ((q / (+ 2)) * (+ 2)) ≡
           0ℤ +ℤ ((q / (+ 2)) * (+ 2))
  digit≡ = cong (λ z → (+ z) +ℤ ((q / (+ 2)) * (+ 2))) eqr
... | suc zero    | _ = inj₂ (q / (+ 2)
                    , trans (trans expand digit≡)
                            (+-comm 1ℤ ((q / (+ 2)) * (+ 2))))
  where
  expand : q ≡ (+ (q % (+ 2))) +ℤ ((q / (+ 2)) * (+ 2))
  expand = a≡a%n+[a/n]*n q (+ 2)

  digit≡ : (+ (q % (+ 2))) +ℤ ((q / (+ 2)) * (+ 2)) ≡
           1ℤ +ℤ ((q / (+ 2)) * (+ 2))
  digit≡ = cong (λ z → (+ z) +ℤ ((q / (+ 2)) * (+ 2))) eqr
... | suc (suc _) | s≤s (s≤s ())

-- If z is divisible by 2^e but not by 2^(e+1), then the e-th dyadic
-- digit of z is 1: subtracting 2^e makes it divisible by 2^(e+1).

private
  lem₁ : ∀ a b c → (a * b) * c ≡ a * (c * b)
  lem₁ = solve 3 (λ a b c → (a :* b) :* c := a :* (c :* b)) refl

  lem₂ : ∀ a b c u → (((a * b) +ℤ u) * c) - (u * c) ≡ a * (c * b)
  lem₂ = solve 4
    (λ a b c u → ((a :* b) :+ u) :* c :- u :* c := a :* (c :* b)) refl

digit : ∀ {z : ℤ} e → pow e ∣ z → ¬ (pow (suc e) ∣ z) →
        pow (suc e) ∣ (z - pow e)
digit {z} e (divides q z≡) ¬div with parity q
... | inj₁ (r , q≡) = contradiction (divides r even) ¬div
  where
  even : z ≡ r * pow (suc e)
  even = trans z≡ (trans (cong (_* pow e) q≡)
    (trans (lem₁ r (+ 2) (pow e)) (cong (r *_) (sym (pow-suc e)))))
... | inj₂ (r , q≡) = divides r odd
  where
  odd : z - pow e ≡ r * pow (suc e)
  odd = trans (cong (_- pow e) (trans z≡ (cong (_* pow e) q≡)))
    (trans (cong ((((r * (+ 2)) +ℤ 1ℤ) * pow e) -_) (sym (*-identityˡ (pow e))))
      (trans (lem₂ r (+ 2) (pow e) 1ℤ) (cong (r *_) (sym (pow-suc e)))))


------------------------------------------------------------------------
-- Closure properties of the order

Ord≤-cong : {P Q : Poly n m} → P ≈[ pow M ] Q → Ord≤ d P → Ord≤ d Q
Ord≤-cong {d = d} {P} {Q} P≈Q ordP γ =
  Eq.subst (pow (val d ∥ γ ∥) ∣_) (cancel (P γ) (Q γ))
    (∣m∣n⇒∣m-n (ordP γ) (∣-trans (pow-∣ (val≤M d ∥ γ ∥)) (P≈Q γ)))
  where
  cancel : ∀ i j → i - (i - j) ≡ j
  cancel = solve 2 (λ i j → i :- (i :- j) := j) refl

Ord≤-+ : {P Q : Poly n m} → Ord≤ d P → Ord≤ d Q → Ord≤ d (P +ᴾ Q)
Ord≤-+ ordP ordQ γ = ∣m∣n⇒∣m+n (ordP γ) (ordQ γ)

Ord≤-∸ : {P Q : Poly n m} → Ord≤ d P → Ord≤ d Q → Ord≤ d (P -ᴾ Q)
Ord≤-∸ ordP ordQ γ = ∣m∣n⇒∣m-n (ordP γ) (ordQ γ)

Ord≤-0ᴾ : Ord≤ d (0ᴾ {n} {m})
Ord≤-0ᴾ _ = i∣0

-- A constant of denominator 2^(d+1) has order d.

Ord≤-κ : ∀ {c : ℤ} → pow (val d 0) ∣ c → Ord≤ d (κ {n} {m} c)
Ord≤-κ {d = d} {n = n} {m = m} {c = c} h γ with γ ≟ᵐ 1ᵐ
... | yes γ≡1ᵐ = Eq.subst (λ z → pow (val d z) ∣ c)
                   (sym (trans (cong ∥_∥ γ≡1ᵐ) (∥1ᵐ∥≡0 {n} {m}))) h
... | no  _    = i∣0

-- The lifting of a linear Boolean form, scaled by 2^(M-d), has
-- order d: a subset of size k contributes a coefficient of
-- denominator 2^(d+1-k), which is of order exactly d.

Ord≤-liftXor : ∀ d (c : Bool) (S : Mon n m) →
               Ord≤ d (pow (val d 1) ·ᴾ liftXor c S)
Ord≤-liftXor d c S γ = ∣-trans
  (pow-∣ (val-bound d 0 (∥ γ ∥) (∥ γ ∥) ℕ.≤-refl))
  (Eq.subst (_∣ (pow (val d 1) * liftXor c S γ)) (pow-+ (val d 1) (∥ γ ∥ ∸ 1))
    (*-monoʳ-∣ (pow (val d 1)) (liftXor-∣ c S γ)))


------------------------------------------------------------------------
-- Lemma 2.13: substitution does not increase the order

subst-Ord≤ : (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m) →
             Ord≤ d P → Ord≤ d (subst P v c S)
subst-Ord≤ {d = d} P v c S ordP γ =
  ∣m∣n⇒∣m+n first (Σmon-∣ _ (λ δ → Σmon-∣ _ (each δ)))
  where
  first : pow (val d ∥ γ ∥) ∣ (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ)
  first with v ∈ᵐ? γ
  ... | yes _ = i∣0
  ... | no  _ = ordP γ

  each : ∀ δ β → pow (val d ∥ γ ∥) ∣ substTerm P v c S γ δ β
  each δ β with v ∈ᵐ? δ
  ... | yes _  = i∣0
  ... | no v∉δ with (δ ∪ᵐ β) ≟ᵐ γ
  ...   | no  _  = i∣0
  ...   | yes eq = ∣-trans (pow-∣ bound) product
    where
    γ≤ : ∥ γ ∥ ≤ ∥ δ ∥ + ∥ β ∥
    γ≤ = Eq.subst (λ z → ∥ z ∥ ≤ ∥ δ ∥ + ∥ β ∥) eq (∥∪ᵐ∥≤ δ β)

    bound : val d ∥ γ ∥ ≤ val d (suc ∥ δ ∥) + (∥ β ∥ ∸ 1)
    bound = val-bound d (∥ δ ∥) (∥ β ∥) (∥ γ ∥) γ≤

    head : pow (val d (suc ∥ δ ∥)) ∣ P (δ ∪ᵐ ⟪ v ⟫)
    head = Eq.subst (λ z → pow (val d z) ∣ P (δ ∪ᵐ ⟪ v ⟫))
             (∥∪ᵐ⟪v⟫∥ δ v v∉δ) (ordP (δ ∪ᵐ ⟪ v ⟫))

    product : pow (val d (suc ∥ δ ∥) + (∥ β ∥ ∸ 1)) ∣
              P (δ ∪ᵐ ⟪ v ⟫) * liftXor c S β
    product = Eq.subst (_∣ (P (δ ∪ᵐ ⟪ v ⟫) * liftXor c S β))
      (pow-+ (val d (suc ∥ δ ∥)) (∥ β ∥ ∸ 1))
      (∣-trans (*-monoˡ-∣ (pow (∥ β ∥ ∸ 1)) head)
               (*-monoʳ-∣ (P (δ ∪ᵐ ⟪ v ⟫)) (liftXor-∣ c S β)))
