------------------------------------------------------------------------
-- Presentations of groups
--
-- The prime field F_p and the binomial coordinates
--
-- Labels and phase exponents both live in F_p = ℤ/pℤ (ForStdlib's
-- ℤ ₚ, residues as Fin p).  The phase coordinates of the paper are the
-- binomials (x choose 2) and (x choose 3) (Section 3.2):
--
--     binom2 x = x (x - 1) / 2,     binom3 x = x (x - 1) (x - 2) / 6.
--
-- The inverses of 2 and 6 are taken from Fermat's little theorem as
-- 2^(p-2) and 6^(p-2), so the binomials are defined for every p; their
-- laws hold when the inverses are genuine, that is for p odd (binom2)
-- and p > 3 (binom3), which is when the quadratic and cubic fragments
-- are admissible.  Written p = 2 + p-2, these conditions read
-- 1 ≤ p-2 and 2 ≤ p-2.
--
-- Polynomial identities are proved with EucDomain's ring solver with
-- integer coefficients, which works over ℤ/pℤ for a symbolic p: the
-- coefficient arithmetic is done in ℤ.  An identity with a division by
-- 2 or 6 is multiplied out first and the factor cancelled (cancel).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Field (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ< ; fromℕ<-cong ; fromℕ<-toℕ ; toℕ<n)
import Data.Integer.Base as ℤ
open import Data.Nat.Base as ℕ using (_≤_ ; s≤s ; z≤n)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; m%n%n≡m%n ; %-distribˡ-+ ; %-distribˡ-*)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

open import Notations using (₀ ; ₁ ; ₁₊)

open import ForStdlib.Data.Fin.Mod
  using (ℤ ; ℤ* ; _+_ ; _*_ ; -_ ; _^′_ ; _＊_ ; +-*-commutativeRing)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')
import Quantum.Synthesis.Ring.Properties.Common as Common

private
  module PM = PrimeModulus' p-2 p-prime

------------------------------------------------------------------------
-- The field

-- The prime.
p : ℕ
p = ₂₊ p-2

F : Set
F = ℤ p

-- The units.
F* : Set
F* = ℤ* p

infixl 6 _-_

_-_ : F → F → F
x - y = x + - y

module FR = CommutativeRing (+-*-commutativeRing p-2)

-- Ring identities with integer coefficients.
module ZS = Common.ZSolver (+-*-commutativeRing p-2)
open ZS public using (solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

-- Numerals, as the solver reads its integer constants.
0F 1F 2F 3F 6F : F
0F = ₀
1F = ₁
2F = ₁ + ₁
3F = 2F + ₁
6F = ((3F + ₁) + ₁) + ₁

-- Fermat's little theorem: c^(p-2) is the inverse of a nonzero c.
infixl 9 _⁻¹ᶠ

_⁻¹ᶠ : F → F
c ⁻¹ᶠ = c ^′ p-2

⁻¹ᶠ-inverseʳ : (c : F) → c ≢ ₀ → c * c ⁻¹ᶠ ≡ 1F
⁻¹ᶠ-inverseʳ c nz = PM.Fermat's-little-theorem (c , nz)

⁻¹ᶠ-inverseˡ : (c : F) → c ≢ ₀ → c ⁻¹ᶠ * c ≡ 1F
⁻¹ᶠ-inverseˡ c nz = trans (FR.*-comm (c ⁻¹ᶠ) c) (⁻¹ᶠ-inverseʳ c nz)

-- A nonzero factor cancels.
cancel : (c : F) → c ≢ ₀ → {a b : F} → c * a ≡ c * b → a ≡ b
cancel c nz {a} {b} e = begin
  a                    ≡⟨ sym (FR.*-identityˡ a) ⟩
  1F * a               ≡⟨ cong (_* a) (sym (⁻¹ᶠ-inverseˡ c nz)) ⟩
  (c ⁻¹ᶠ * c) * a      ≡⟨ FR.*-assoc (c ⁻¹ᶠ) c a ⟩
  c ⁻¹ᶠ * (c * a)      ≡⟨ cong (c ⁻¹ᶠ *_) e ⟩
  c ⁻¹ᶠ * (c * b)      ≡⟨ sym (FR.*-assoc (c ⁻¹ᶠ) c b) ⟩
  (c ⁻¹ᶠ * c) * b      ≡⟨ cong (_* b) (⁻¹ᶠ-inverseˡ c nz) ⟩
  1F * b               ≡⟨ FR.*-identityˡ b ⟩
  b                    ∎
  where open ≡-Reasoning

-- A product of nonzero elements is nonzero.
*-nonzero : {a b : F} → a ≢ ₀ → b ≢ ₀ → a * b ≢ ₀
*-nonzero {a} {b} na nb = proj₂ (PM._*'_ (a , na) (b , nb))

------------------------------------------------------------------------
-- 2 and 6 are invertible in the admissible fragments

private
  two≢0′ : ∀ m → 1 ≤ m → _≢_ {A = ℤ (₂₊ m)} (₁ + ₁) ₀
  two≢0′ ℕ.zero    ()
  two≢0′ (ℕ.suc k) _ ()

  three≢0′ : ∀ m → 2 ≤ m → _≢_ {A = ℤ (₂₊ m)} ((₁ + ₁) + ₁) ₀
  three≢0′ ℕ.zero           ()
  three≢0′ (ℕ.suc ℕ.zero)   (s≤s ())
  three≢0′ (ℕ.suc (ℕ.suc k)) _ ()

two≢0 : 1 ≤ p-2 → 2F ≢ ₀
two≢0 = two≢0′ p-2

three≢0 : 2 ≤ p-2 → 3F ≢ ₀
three≢0 = three≢0′ p-2

six≡2*3 : 6F ≡ 2F * 3F
six≡2*3 = solve 0 (con (ℤ.+ 6) := con (ℤ.+ 2) :* con (ℤ.+ 3)) refl

-- The cubic condition implies the quadratic one.
big⇒odd : 2 ≤ p-2 → 1 ≤ p-2
big⇒odd (s≤s _) = s≤s z≤n

six≢0 : 2 ≤ p-2 → 6F ≢ ₀
six≢0 h e = *-nonzero (two≢0 (big⇒odd h)) (three≢0 h) (trans (sym six≡2*3) e)

-- The two inverses.
half sixth : F
half = 2F ⁻¹ᶠ
sixth = 6F ⁻¹ᶠ

------------------------------------------------------------------------
-- k-fold sums are products

-- The residue of a natural number.
⟨_⟩ : ℕ → F
⟨ m ⟩ = fromℕ< (m%n<n m p)

＊-* : (m : ℕ) (x : F) → m ＊ x ≡ fromℕ< (m%n<n (m ℕ.* toℕ x) p)
＊-* ℕ.zero    x = refl
＊-* (ℕ.suc m) x = begin
  x + (m ＊ x)
    ≡⟨ cong (x +_) (＊-* m x) ⟩
  fromℕ< (m%n<n (toℕ x ℕ.+ toℕ (fromℕ< (m%n<n (m ℕ.* toℕ x) p))) p)
    ≡⟨ fromℕ<-cong _ _ eq (m%n<n (toℕ x ℕ.+ toℕ (fromℕ< (m%n<n (m ℕ.* toℕ x) p))) p)
                          (m%n<n (toℕ x ℕ.+ m ℕ.* toℕ x) p) ⟩
  fromℕ< (m%n<n (ℕ.suc m ℕ.* toℕ x) p)
    ∎
  where
  open ≡-Reasoning
  eq : (toℕ x ℕ.+ toℕ (fromℕ< (m%n<n (m ℕ.* toℕ x) p))) % p ≡ (toℕ x ℕ.+ m ℕ.* toℕ x) % p
  eq = begin
    (toℕ x ℕ.+ toℕ (fromℕ< (m%n<n (m ℕ.* toℕ x) p))) % p
      ≡⟨ cong (λ t → (toℕ x ℕ.+ t) % p) (toℕ-fromℕ< (m%n<n (m ℕ.* toℕ x) p)) ⟩
    (toℕ x ℕ.+ (m ℕ.* toℕ x) % p) % p
      ≡⟨ %-distribˡ-+ (toℕ x) ((m ℕ.* toℕ x) % p) p ⟩
    (toℕ x % p ℕ.+ (m ℕ.* toℕ x) % p % p) % p
      ≡⟨ cong (λ t → (toℕ x % p ℕ.+ t) % p) (m%n%n≡m%n (m ℕ.* toℕ x) p) ⟩
    (toℕ x % p ℕ.+ (m ℕ.* toℕ x) % p) % p
      ≡⟨ sym (%-distribˡ-+ (toℕ x) (m ℕ.* toℕ x) p) ⟩
    (toℕ x ℕ.+ m ℕ.* toℕ x) % p
      ∎

-- A residue as a count: toℕ k copies of x make k * x.
＊-toℕ : (k x : F) → toℕ k ＊ x ≡ k * x
＊-toℕ k x = ＊-* (toℕ k) x

------------------------------------------------------------------------
-- The binomial coordinates

binom2 binom3 : F → F
binom2 x = x * (x - 1F) * half
binom3 x = x * (x - 1F) * (x - 2F) * sixth

module Odd (odd : 1 ≤ p-2) where

  2*half : 2F * half ≡ 1F
  2*half = ⁻¹ᶠ-inverseʳ 2F (two≢0 odd)

  -- 2 (x choose 2) = x (x - 1).
  2*binom2 : (x : F) → 2F * binom2 x ≡ x * (x - 1F)
  2*binom2 x = begin
    2F * (x * (x - 1F) * half)    ≡⟨ solve 3 (λ c u h → c :* (u :* h) := u :* (c :* h)) refl 2F (x * (x - 1F)) half ⟩
    x * (x - 1F) * (2F * half)    ≡⟨ cong (x * (x - 1F) *_) 2*half ⟩
    x * (x - 1F) * 1F             ≡⟨ FR.*-identityʳ _ ⟩
    x * (x - 1F)                  ∎
    where open ≡-Reasoning

  -- Equations between expressions in binom2, proved doubled.
  by-doubling : {a b : F} → 2F * a ≡ 2F * b → a ≡ b
  by-doubling = cancel 2F (two≢0 odd)

  -- Lemma 5 (Pascal identities in the quadratic coordinate).
  binom2-shift : (x : F) → binom2 (x + 1F) ≡ binom2 x + x
  binom2-shift x = by-doubling (begin
    2F * binom2 (x + 1F)         ≡⟨ 2*binom2 (x + 1F) ⟩
    (x + 1F) * ((x + 1F) - 1F)   ≡⟨ solve 1 (λ x → (x :+ con (ℤ.+ 1)) :* ((x :+ con (ℤ.+ 1)) :- con (ℤ.+ 1))
                                                   := x :* (x :- con (ℤ.+ 1)) :+ con (ℤ.+ 2) :* x) refl x ⟩
    x * (x - 1F) + 2F * x        ≡⟨ cong (_+ 2F * x) (sym (2*binom2 x)) ⟩
    2F * binom2 x + 2F * x       ≡⟨ sym (FR.distribˡ 2F (binom2 x) x) ⟩
    2F * (binom2 x + x)          ∎)
    where open ≡-Reasoning

  binom2-add : (x y : F) → binom2 (x + y) ≡ binom2 x + binom2 y + x * y
  binom2-add x y = by-doubling (begin
    2F * binom2 (x + y)
      ≡⟨ 2*binom2 (x + y) ⟩
    (x + y) * ((x + y) - 1F)
      ≡⟨ solve 2 (λ x y → (x :+ y) :* ((x :+ y) :- con (ℤ.+ 1))
                         := x :* (x :- con (ℤ.+ 1)) :+ y :* (y :- con (ℤ.+ 1)) :+ con (ℤ.+ 2) :* (x :* y)) refl x y ⟩
    x * (x - 1F) + y * (y - 1F) + 2F * (x * y)
      ≡⟨ cong₂ (λ a b → a + b + 2F * (x * y)) (sym (2*binom2 x)) (sym (2*binom2 y)) ⟩
    2F * binom2 x + 2F * binom2 y + 2F * (x * y)
      ≡⟨ solve 4 (λ c a b d → c :* a :+ c :* b :+ c :* d := c :* (a :+ b :+ d)) refl 2F (binom2 x) (binom2 y) (x * y) ⟩
    2F * (binom2 x + binom2 y + x * y)
      ∎)
    where open ≡-Reasoning

  binom2-scale : (k x : F) → binom2 (k * x) ≡ k * k * binom2 x + binom2 k * x
  binom2-scale k x = by-doubling (begin
    2F * binom2 (k * x)
      ≡⟨ 2*binom2 (k * x) ⟩
    (k * x) * (k * x - 1F)
      ≡⟨ solve 2 (λ k x → (k :* x) :* (k :* x :- con (ℤ.+ 1))
                         := k :* k :* (x :* (x :- con (ℤ.+ 1))) :+ (k :* (k :- con (ℤ.+ 1))) :* x) refl k x ⟩
    k * k * (x * (x - 1F)) + (k * (k - 1F)) * x
      ≡⟨ cong₂ (λ a b → k * k * a + b * x) (sym (2*binom2 x)) (sym (2*binom2 k)) ⟩
    k * k * (2F * binom2 x) + (2F * binom2 k) * x
      ≡⟨ solve 5 (λ c k a b x → k :* k :* (c :* a) :+ (c :* b) :* x := c :* (k :* k :* a :+ b :* x))
               refl 2F k (binom2 x) (binom2 k) x ⟩
    2F * (k * k * binom2 x + binom2 k * x)
      ∎)
    where open ≡-Reasoning

module Big (big : 2 ≤ p-2) where

  open Odd (big⇒odd big) public

  6*sixth : 6F * sixth ≡ 1F
  6*sixth = ⁻¹ᶠ-inverseʳ 6F (six≢0 big)

  -- 6 (x choose 3) = x (x - 1) (x - 2).
  6*binom3 : (x : F) → 6F * binom3 x ≡ x * (x - 1F) * (x - 2F)
  6*binom3 x = begin
    6F * (x * (x - 1F) * (x - 2F) * sixth)  ≡⟨ solve 3 (λ c u s → c :* (u :* s) := u :* (c :* s)) refl 6F (x * (x - 1F) * (x - 2F)) sixth ⟩
    x * (x - 1F) * (x - 2F) * (6F * sixth)  ≡⟨ cong (x * (x - 1F) * (x - 2F) *_) 6*sixth ⟩
    x * (x - 1F) * (x - 2F) * 1F            ≡⟨ FR.*-identityʳ _ ⟩
    x * (x - 1F) * (x - 2F)                 ∎
    where open ≡-Reasoning

  -- 6 (x choose 2) = 3 x (x - 1).
  6*binom2 : (x : F) → 6F * binom2 x ≡ 3F * (x * (x - 1F))
  6*binom2 x = begin
    6F * binom2 x          ≡⟨ cong (_* binom2 x) six≡2*3 ⟩
    2F * 3F * binom2 x     ≡⟨ solve 3 (λ a b c → a :* b :* c := b :* (a :* c)) refl 2F 3F (binom2 x) ⟩
    3F * (2F * binom2 x)   ≡⟨ cong (3F *_) (2*binom2 x) ⟩
    3F * (x * (x - 1F))    ∎
    where open ≡-Reasoning

  by-sextupling : {a b : F} → 6F * a ≡ 6F * b → a ≡ b
  by-sextupling = cancel 6F (six≢0 big)

  -- Lemma 6 (Pascal identities in the cubic coordinate).
  binom3-shift : (x : F) → binom3 (x + 1F) ≡ binom3 x + binom2 x
  binom3-shift x = by-sextupling (begin
    6F * binom3 (x + 1F)
      ≡⟨ 6*binom3 (x + 1F) ⟩
    (x + 1F) * ((x + 1F) - 1F) * ((x + 1F) - 2F)
      ≡⟨ solve 1 (λ x → (x :+ con (ℤ.+ 1)) :* ((x :+ con (ℤ.+ 1)) :- con (ℤ.+ 1)) :* ((x :+ con (ℤ.+ 1)) :- con (ℤ.+ 2))
                       := x :* (x :- con (ℤ.+ 1)) :* (x :- con (ℤ.+ 2)) :+ con (ℤ.+ 3) :* (x :* (x :- con (ℤ.+ 1)))) refl x ⟩
    x * (x - 1F) * (x - 2F) + 3F * (x * (x - 1F))
      ≡⟨ cong₂ _+_ (sym (6*binom3 x)) (sym (6*binom2 x)) ⟩
    6F * binom3 x + 6F * binom2 x
      ≡⟨ sym (FR.distribˡ 6F (binom3 x) (binom2 x)) ⟩
    6F * (binom3 x + binom2 x)
      ∎)
    where open ≡-Reasoning

  binom3-add : (x y : F) →
               binom3 (x + y) ≡ binom3 x + binom3 y + binom2 x * y + x * binom2 y
  binom3-add x y = by-sextupling (begin
    6F * binom3 (x + y)
      ≡⟨ 6*binom3 (x + y) ⟩
    (x + y) * ((x + y) - 1F) * ((x + y) - 2F)
      ≡⟨ solve 2 (λ x y → (x :+ y) :* ((x :+ y) :- con (ℤ.+ 1)) :* ((x :+ y) :- con (ℤ.+ 2))
                         := x :* (x :- con (ℤ.+ 1)) :* (x :- con (ℤ.+ 2))
                            :+ y :* (y :- con (ℤ.+ 1)) :* (y :- con (ℤ.+ 2))
                            :+ con (ℤ.+ 3) :* (x :* (x :- con (ℤ.+ 1))) :* y
                            :+ x :* (con (ℤ.+ 3) :* (y :* (y :- con (ℤ.+ 1))))) refl x y ⟩
    x * (x - 1F) * (x - 2F) + y * (y - 1F) * (y - 2F) + 3F * (x * (x - 1F)) * y + x * (3F * (y * (y - 1F)))
      ≡⟨ cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (sym (6*binom3 x)) (sym (6*binom3 y))) (cong (_* y) (sym (6*binom2 x))))
                   (cong (x *_) (sym (6*binom2 y))) ⟩
    6F * binom3 x + 6F * binom3 y + 6F * binom2 x * y + x * (6F * binom2 y)
      ≡⟨ solve 7 (λ c a b u y x v → c :* a :+ c :* b :+ c :* u :* y :+ x :* (c :* v)
                                   := c :* (a :+ b :+ u :* y :+ x :* v))
               refl 6F (binom3 x) (binom3 y) (binom2 x) y x (binom2 y) ⟩
    6F * (binom3 x + binom3 y + binom2 x * y + x * binom2 y)
      ∎)
    where open ≡-Reasoning

  binom3-scale : (k x : F) →
                 binom3 (k * x) ≡ k * k * k * binom3 x + 2F * k * binom2 k * binom2 x + binom3 k * x
  binom3-scale k x = by-sextupling (begin
    6F * binom3 (k * x)
      ≡⟨ 6*binom3 (k * x) ⟩
    (k * x) * (k * x - 1F) * (k * x - 2F)
      ≡⟨ solve 2 (λ k x → (k :* x) :* (k :* x :- con (ℤ.+ 1)) :* (k :* x :- con (ℤ.+ 2))
                         := k :* k :* k :* (x :* (x :- con (ℤ.+ 1)) :* (x :- con (ℤ.+ 2)))
                            :+ k :* (k :* (k :- con (ℤ.+ 1))) :* (con (ℤ.+ 3) :* (x :* (x :- con (ℤ.+ 1))))
                            :+ k :* (k :- con (ℤ.+ 1)) :* (k :- con (ℤ.+ 2)) :* x) refl k x ⟩
    k * k * k * (x * (x - 1F) * (x - 2F)) + k * (k * (k - 1F)) * (3F * (x * (x - 1F)))
      + k * (k - 1F) * (k - 2F) * x
      ≡⟨ cong₂ _+_ (cong₂ _+_ (cong (k * k * k *_) (sym (6*binom3 x)))
                              (cong₂ (λ a b → k * a * b) (sym (2*binom2 k)) (sym (6*binom2 x))))
                   (cong (_* x) (sym (6*binom3 k))) ⟩
    k * k * k * (6F * binom3 x) + k * (2F * binom2 k) * (6F * binom2 x) + 6F * binom3 k * x
      ≡⟨ solve 8 (λ c d k a b u t x → k :* k :* k :* (c :* a) :+ k :* (d :* b) :* (c :* u) :+ c :* t :* x
                                      := c :* (k :* k :* k :* a :+ d :* k :* b :* u :+ t :* x))
               refl 6F 2F k (binom3 x) (binom2 k) (binom2 x) (binom3 k) x ⟩
    6F * (k * k * k * binom3 x + 2F * k * binom2 k * binom2 x + binom3 k * x)
      ∎)
    where open ≡-Reasoning
