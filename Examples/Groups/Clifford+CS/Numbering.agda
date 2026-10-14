------------------------------------------------------------------------
-- Presentations of groups
--
-- The numbering of the basis vectors on n qubits by the Gray code
--
-- From four wires on the auxiliary language is P′ (Auxiliary.P), whose
-- letters are indexed by `Fin N` with N the number of basis vectors,
-- and the index of a basis vector is its position in the reflected
-- Gray code (Real-Clifford+CH.Auxiliary.Gray), so that consecutive
-- indices differ at one wire — which is what lets a letter on two
-- consecutive indices decode to a gate on that wire.
--
-- The auxiliary development takes N as a successor, `suc N′`, so that
-- the index 0 of its coset representatives is the constructor `zero`;
-- here N′ is 2ⁿ − 1, and `N≡` says the two spellings of N agree.  The
-- Gray code lives at `Fin (2 ^ n)`, so the numbering goes through a
-- cast, which the laws below absorb once and for all: `cod` reads a
-- basis vector off an index and `idx` an index off a basis vector,
-- mutually inverse.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Numbering (n : ℕ) where

open import Data.Fin using (Fin ; cast)
open import Data.Fin.Properties using (cast-trans ; cast-is-id)
open import Data.Nat using (zero ; suc ; _+_ ; _*_ ; _∸_ ; _<_ ; _≤_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (m^n>0 ; ^-distribˡ-+-* ; *-monoʳ-≤ ; ≤-trans ; ≤-reflexive ; *-identityʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Clifford+CS.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code)

------------------------------------------------------------------------
-- The number of basis vectors, as a successor

N′ : ℕ
N′ = 2 ^ n ∸ 1

N : ℕ
N = suc N′

private
  suc-∸ : ∀ (m : ℕ) → 0 < m → suc (m ∸ 1) ≡ m
  suc-∸ (suc k) _ = Eq.refl

N≡ : N ≡ 2 ^ n
N≡ = suc-∸ (2 ^ n) (m^n>0 2 n)

------------------------------------------------------------------------
-- The numbering

cod : Fin N → Bits n
cod k = code n (cast N≡ k)

idx : Bits n → Fin N
idx x = cast (Eq.sym N≡) (index n x)

cod-idx : ∀ (x : Bits n) → cod (idx x) ≡ x
cod-idx x =
  Eq.trans (Eq.cong (code n) (cast-trans (Eq.sym N≡) N≡ (index n x)))
    (Eq.trans (Eq.cong (code n) (cast-is-id Eq.refl (index n x)))
              (code-index n x))

idx-cod : ∀ (k : Fin N) → idx (cod k) ≡ k
idx-cod k =
  Eq.trans (Eq.cong (cast (Eq.sym N≡)) (index-code n (cast N≡ k)))
    (Eq.trans (cast-trans N≡ (Eq.sym N≡) k) (cast-is-id Eq.refl k))

idx-inj : ∀ {x y : Bits n} → idx x ≡ idx y → x ≡ y
idx-inj {x} {y} e =
  Eq.trans (Eq.sym (cod-idx x)) (Eq.trans (Eq.cong cod e) (cod-idx y))

cod-inj : ∀ {k l : Fin N} → cod k ≡ cod l → k ≡ l
cod-inj {k} {l} e =
  Eq.trans (Eq.sym (idx-cod k)) (Eq.trans (Eq.cong idx e) (idx-cod l))

------------------------------------------------------------------------
-- Sixteen basis vectors from four wires on

16≤2^ : ∀ (m : ℕ) → 16 ≤ 2 ^ (4 + m)
16≤2^ m = ≤-trans (≤-reflexive (Eq.sym (*-identityʳ 16)))
                  (≤-trans (*-monoʳ-≤ 16 (m^n>0 2 m))
                           (≤-reflexive (Eq.sym (^-distribˡ-+-* 2 4 m))))
