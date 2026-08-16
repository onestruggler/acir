------------------------------------------------------------------------
-- Presentations of groups
--
-- (p² - 1)/8, as an element of ℤ/pℤ.
--
-- Clifford.Qupit.Syntactics gives order-SH the correction ω^((p²-1)/8),
-- and Clifford.Qupit.SemLocal computes the phase that rule actually
-- carries: -h·σ², with h = ½ and σ = -½, i.e. -⅛.  This file is the
-- bridge — that the residue of (p²-1)/8 IS -⅛ — and it is elementary
-- number theory with no circuits in it.
--
-- Two halves.
--
--   * ℕ.  p is odd (it is a prime bigger than 2), so p = 1 + 2q, and
--     q(q+1) is even, so p² = 1 + 8t.  Hence the division by 8 is exact
--     and (p²-1)/8 is that t.
--   * ℤ/pℤ.  `mult` is a ring homomorphism ℕ → ℤ/pℤ killing p, so
--     8·mult t = mult (p² - 1) = -1.  Multiplying by ⅛ — which is
--     legitimate because (2·½)³ = 1, so no inverse of 8 ever has to be
--     constructed — gives mult t = -⅛.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemSHExp
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  where

open import Data.Nat as Nat using (zero ; _∸_)
open import Data.Nat.Divisibility using (_∣_ ; divides)
open import Data.Nat.DivMod using (_/_ ; _%_ ; m*n/n≡m ; m≡m%n+[m/n]*n)
open import Data.Nat.Primality using (prime⇒irreducible)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq

open import Algebra.Properties.Ring (+-*-ring p-2) using (-1*x≈-x)
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-p)

import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem

open +-*-Solver using (_:=_ ; _:+_ ; _:*_ ; con) renaming (solve to nsolve)

------------------------------------------------------------------------
-- Parity in ℕ
--
-- Every natural is even or odd, and the odd branch is what primality
-- will select for p.  The arithmetic in each step is the ℕ ring solver.

parity : ∀ m → (∃ λ q → m ≡ 2 Nat.* q) ⊎ (∃ λ q → m ≡ 1 Nat.+ 2 Nat.* q)
parity zero      = inj₁ (0 , Eq.refl)
parity (₁₊ zero) = inj₂ (0 , Eq.refl)
parity (₂₊ m) with parity m
... | inj₁ (q , e) =
  inj₁ (₁₊ q , Eq.trans (Eq.cong (λ z → 2 Nat.+ z) e) (grow q))
  where
  grow : ∀ q → 2 Nat.+ 2 Nat.* q ≡ 2 Nat.* (1 Nat.+ q)
  grow = nsolve 1 (λ q → con 2 :+ con 2 :* q := con 2 :* (con 1 :+ q)) Eq.refl
... | inj₂ (q , e) =
  inj₂ (₁₊ q , Eq.trans (Eq.cong (λ z → 2 Nat.+ z) e) (grow q))
  where
  grow : ∀ q → 2 Nat.+ (1 Nat.+ 2 Nat.* q) ≡ 1 Nat.+ 2 Nat.* (1 Nat.+ q)
  grow = nsolve 1 (λ q → con 2 :+ (con 1 :+ con 2 :* q)
                          := con 1 :+ con 2 :* (con 1 :+ q))
                Eq.refl

-- The product of two consecutive naturals is even.
tri : ∀ m → ∃ λ t → m Nat.* (1 Nat.+ m) ≡ 2 Nat.* t
tri m with parity m
... | inj₁ (r , e) =
    r Nat.* (1 Nat.+ 2 Nat.* r)
  , Eq.trans (Eq.cong (λ z → z Nat.* (1 Nat.+ z)) e) (ev r)
  where
  ev : ∀ r → (2 Nat.* r) Nat.* (1 Nat.+ 2 Nat.* r)
               ≡ 2 Nat.* (r Nat.* (1 Nat.+ 2 Nat.* r))
  ev = nsolve 1 (λ r → (con 2 :* r) :* (con 1 :+ con 2 :* r)
                        := con 2 :* (r :* (con 1 :+ con 2 :* r)))
              Eq.refl
... | inj₂ (r , e) =
    (1 Nat.+ 2 Nat.* r) Nat.* (1 Nat.+ r)
  , Eq.trans (Eq.cong (λ z → z Nat.* (1 Nat.+ z)) e) (od r)
  where
  od : ∀ r → (1 Nat.+ 2 Nat.* r) Nat.* (1 Nat.+ (1 Nat.+ 2 Nat.* r))
               ≡ 2 Nat.* ((1 Nat.+ 2 Nat.* r) Nat.* (1 Nat.+ r))
  od = nsolve 1 (λ r → (con 1 :+ con 2 :* r) :* (con 1 :+ (con 1 :+ con 2 :* r))
                        := con 2 :* ((con 1 :+ con 2 :* r) :* (con 1 :+ r)))
              Eq.refl

------------------------------------------------------------------------
-- p is odd
--
-- If it were even, 2 would divide it; but an irreducible number's only
-- divisors are 1 and itself, and p is at least 3.

p-odd : ∃ λ q → p ≡ 1 Nat.+ 2 Nat.* q
p-odd with parity p
... | inj₂ r       = r
... | inj₁ (q , e)
        with prime⇒irreducible p-prime (divides q (Eq.trans e (NP.*-comm 2 q)))
...        | inj₁ ()
...        | inj₂ ()

------------------------------------------------------------------------
-- ... so p² is one more than eight times something
--
-- p² = (1 + 2q)² = 1 + 4·q(q+1), and q(q+1) is even.

eighth : ∃ λ t → p Nat.* p ≡ 1 Nat.+ 8 Nat.* t
eighth =
  t , Eq.trans (Eq.cong (λ z → z Nat.* z) (proj₂ p-odd)) step
  where
  q = proj₁ p-odd
  t = proj₁ (tri q)

  sq : ∀ q → (1 Nat.+ 2 Nat.* q) Nat.* (1 Nat.+ 2 Nat.* q)
               ≡ 1 Nat.+ 4 Nat.* (q Nat.* (1 Nat.+ q))
  sq = nsolve 1 (λ q → (con 1 :+ con 2 :* q) :* (con 1 :+ con 2 :* q)
                        := con 1 :+ con 4 :* (q :* (con 1 :+ q)))
              Eq.refl

  four : ∀ t → 1 Nat.+ 4 Nat.* (2 Nat.* t) ≡ 1 Nat.+ 8 Nat.* t
  four = nsolve 1 (λ t → con 1 :+ con 4 :* (con 2 :* t) := con 1 :+ con 8 :* t)
                Eq.refl

  step : (1 Nat.+ 2 Nat.* q) Nat.* (1 Nat.+ 2 Nat.* q) ≡ 1 Nat.+ 8 Nat.* t
  step = Eq.trans (sq q)
           (Eq.trans (Eq.cong (λ z → 1 Nat.+ 4 Nat.* z) (proj₂ (tri q)))
                     (four t))

-- ... so the division by 8 in `sh-exponent` is exact.

sh-exponent : ℕ
sh-exponent = (p Nat.* p ∸ 1) / 8

sh-exponent≡ : sh-exponent ≡ proj₁ eighth
sh-exponent≡ =
  Eq.trans (Eq.cong (λ z → (z ∸ 1) / 8) (proj₂ eighth))
    (Eq.trans (Eq.cong (_/ 8) (NP.*-comm 8 (proj₁ eighth)))
              (m*n/n≡m (proj₁ eighth) 8))

------------------------------------------------------------------------
-- mult is a ring homomorphism

mult-+ : ∀ m k → mult (m Nat.+ k) ≡ mult m + mult k
mult-+ zero   k = Eq.sym (+-identityˡ (mult k))
mult-+ (₁₊ m) k =
  Eq.trans (Eq.cong (₁ +_) (mult-+ m k))
           (Eq.sym (+-assoc ₁ (mult m) (mult k)))

mult-* : ∀ m k → mult (m Nat.* k) ≡ mult m * mult k
mult-* zero   k = Eq.sym (*-zeroˡ (mult k))
mult-* (₁₊ m) k =
  Eq.trans (mult-+ k (m Nat.* k))
    (Eq.trans (Eq.cong (mult k +_) (mult-* m k))
      (Eq.sym (Eq.trans (*-distribʳ-+ (mult k) ₁ (mult m))
                        (Eq.cong (_+ mult m * mult k) (*-identityˡ (mult k))))))

mult-1 : mult 1 ≡ ₁
mult-1 = +-identityʳ ₁

-- ... so it only sees a natural through its residue.  This is what
-- identifies it with SemRealises' `modp`.
mult-mod : ∀ k → mult k ≡ mult (k % p)
mult-mod k =
  Eq.trans (Eq.cong mult (m≡m%n+[m/n]*n k p))
    (Eq.trans (mult-+ (k % p) ((k / p) Nat.* p))
      (Eq.trans (Eq.cong (mult (k % p) +_)
                   (Eq.trans (mult-* (k / p) p)
                      (Eq.trans (Eq.cong (mult (k / p) *_) mult-p)
                                (*-zeroʳ (mult (k / p))))))
                (+-identityʳ (mult (k % p)))))

------------------------------------------------------------------------
-- The value
--
-- 8·mult t = -1, and 8·⅛ = (2·½)³ = 1, so mult t = -⅛ without an
-- inverse of 8 ever being formed.

h : ℤ ₚ
h = Sem.1/2

private
  -- 2·½ = 1, from Semantics' half+half, with 2 spelled as `mult 2`.
  two-h : mult 2 * h ≡ ₁
  two-h =
    Eq.trans (*-distribʳ-+ h ₁ (₁ + ₀))
      (Eq.trans (Eq.cong₂ _+_ (*-identityˡ h)
                   (Eq.trans (Eq.cong (_* h) (+-identityʳ ₁)) (*-identityˡ h)))
                Sem.half+half)

  eight : ℤ ₚ
  eight = mult 2 * (mult 2 * mult 2)

  mult-8 : mult 8 ≡ eight
  mult-8 = Eq.trans (mult-* 2 4) (Eq.cong (mult 2 *_) (mult-* 2 2))

  -- Rearranged so that each 2 meets its own ½.
  regroup : ∀ (x y : ℤ ₚ) →
            (x * (x * x)) * (y * (y * y)) ≡ (x * y) * ((x * y) * (x * y))
  regroup = solve p-2 2
    (λ x y → ((x ⊗ (x ⊗ x)) ⊗ (y ⊗ (y ⊗ y))) ,
             ((x ⊗ y) ⊗ ((x ⊗ y) ⊗ (x ⊗ y))))
    (λ {_} {_} → Eq.refl)

  eight-h : eight * (h * (h * h)) ≡ ₁
  eight-h =
    Eq.trans (regroup (mult 2) h)
      (Eq.trans (Eq.cong (λ z → z * (z * z)) two-h)
                (Eq.trans (Eq.cong (₁ *_) (*-identityˡ ₁)) (*-identityˡ ₁)))

  mult-p² : mult (p Nat.* p) ≡ ₀
  mult-p² = Eq.trans (mult-* p p)
              (Eq.trans (Eq.cong (_* mult p) mult-p) (*-zeroˡ (mult p)))

  -- mult (8t) = -1, since 1 + 8t is p².
  mult-8t : mult (8 Nat.* proj₁ eighth) ≡ - ₁
  mult-8t =
    Eq.trans (Eq.sym (+-identityˡ X))
      (Eq.trans (Eq.cong (_+ X) (Eq.sym (+-inverseˡ ₁)))
        (Eq.trans (+-assoc (- ₁) ₁ X)
          (Eq.trans (Eq.cong ((- ₁) +_) e0) (+-identityʳ (- ₁)))))
    where
    X : ℤ ₚ
    X = mult (8 Nat.* proj₁ eighth)

    e0 : ₁ + X ≡ ₀
    e0 = Eq.trans
           (Eq.sym (Eq.trans (Eq.cong mult (proj₂ eighth))
                     (Eq.trans (mult-+ 1 (8 Nat.* proj₁ eighth))
                               (Eq.cong (_+ X) mult-1))))
           mult-p²

  key : eight * mult sh-exponent ≡ - ₁
  key =
    Eq.trans (Eq.cong (_* mult sh-exponent) (Eq.sym mult-8))
      (Eq.trans (Eq.sym (mult-* 8 sh-exponent))
        (Eq.trans (Eq.cong (λ z → mult (8 Nat.* z)) sh-exponent≡) mult-8t))

sh-value : mult sh-exponent ≡ - (h * (h * h))
sh-value =
  Eq.trans (Eq.sym (*-identityʳ (mult sh-exponent)))
    (Eq.trans (Eq.cong (mult sh-exponent *_) (Eq.sym eight-h))
      (Eq.trans (Eq.sym (*-assoc (mult sh-exponent) eight (h * (h * h))))
        (Eq.trans (Eq.cong (_* (h * (h * h)))
                     (Eq.trans (*-comm (mult sh-exponent) eight) key))
                  (-1*x≈-x (h * (h * h))))))
