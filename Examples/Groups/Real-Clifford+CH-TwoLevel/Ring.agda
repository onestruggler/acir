------------------------------------------------------------------------
-- Presentations of groups
--
-- The ring ℤ[1/√2] of Fang, Heunen and Kaarsgaard, "Hadamard-Pi:
-- Equational Quantum Programming" (POPL 2026, arXiv:2506.06835), §4:
-- the entries of the orthogonal matrices Oₙ(ℤ[1/√2]), taken from
-- EucDomain as 𝔻[√2] = ℤ[½][√2] (DRootTwo), with ℤ[√2] (ZRootTwo).
--
-- An element a + b √2 is written RootTwo a b.
--
-- As in Clifford+T-2qubit-TwoLevel.Ring, the operations of 𝔻[√2] are
-- opaque: its elements are records of dyadic fractions, themselves
-- records, and comparing two convertible but different expressions
-- would otherwise unfold the dyadic arithmetic on stuck terms.
-- Computations that need the arithmetic go in `opaque unfolding`
-- blocks.  Conjugation is the identity on these real numbers, so the
-- unitary matrices over 𝔻[√2] are the orthogonal ones.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec)

open import Instances
  using (_≟_ ; SemiRing ; Ring ; Adjoint ; _+_ ; _*_ ; -_ ; 0# ; 1# ; fromℕ ; adj)
open import Quantum.Synthesis.Ring
  using ( Dyadic ; Dyadic' ; _[√2] ; RootTwo ; DRootTwo ; ZRootTwo
        ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; DecEqDyadic
        ; SemiRingRootTwo ; RingRootTwo ; AdjointRootTwo ; DecEqRootTwo )
open import Quantum.Synthesis.Ring.Properties
  using ( isCommutativeRing-DRootTwo ; commutativeRing-ZRootTwo ; commutativeRing-𝔻
        ; IsInvolutiveRingEndo ; adj-DRootTwo )
import Quantum.Synthesis.Ring.Properties.Common as Common

------------------------------------------------------------------------
-- The two rings

-- 𝔻[√2] = ℤ[1/√2], the ring of the matrix entries.
D : Set
D = DRootTwo

-- ℤ[√2].
Z : Set
Z = ZRootTwo

-- The operations of 𝔻[√2]: EucDomain's, made opaque, and conjugation.
opaque
  infixl 6 _+ᴰ_
  infixl 7 _*ᴰ_
  infix 8 -ᴰ_

  _+ᴰ_ _*ᴰ_ : D → D → D
  x +ᴰ y = x + y
  x *ᴰ y = x * y

  -ᴰ_ : D → D
  -ᴰ x = - x

  adjᴰ : D → D
  adjᴰ x = adj x

0ᴰ 1ᴰ : D
0ᴰ = 0#
1ᴰ = 1#

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  isCommutativeRing-D : IsCommutativeRing _≡_ _+ᴰ_ _*ᴰ_ -ᴰ_ 0ᴰ 1ᴰ
  isCommutativeRing-D = isCommutativeRing-DRootTwo

commutativeRing-D : CommutativeRing 0ℓ 0ℓ
commutativeRing-D = record { isCommutativeRing = isCommutativeRing-D }

-- The ring structures: 𝔻[√2]'s opaque one, and EucDomain's for the
-- dyadic fractions and for ℤ[√2].
module 𝔻R = CommutativeRing commutativeRing-𝔻
module DR = CommutativeRing commutativeRing-D
module ZR = CommutativeRing commutativeRing-ZRootTwo

-- Ring solvers with integer coefficients.
module DS = Common.ZSolver commutativeRing-D
module ZS = Common.ZSolver commutativeRing-ZRootTwo

------------------------------------------------------------------------
-- Constants

private
  d0 d1 h : Dyadic
  d0 = Dyadic' (+ 0) 0 _
  d1 = Dyadic' (+ 1) 0 _
  h = Dyadic' (+ 1) 1 _

-- 1/√2 = √2 / 2, the scalar of the Hadamard matrix, and -1.
√½ -1ᴰ : D
√½ = RootTwo d0 h
-1ᴰ = RootTwo (Dyadic' -[1+ 0 ] 0 _) d0

------------------------------------------------------------------------
-- Instances

-- Decidable equality.
infix 4 _≟ᴰ_ _≟ᶻ_

_≟ᴰ_ : (x y : D) → Dec (x ≡ y)
_≟ᴰ_ = _≟_

_≟ᶻ_ : (x y : Z) → Dec (x ≡ y)
_≟ᶻ_ = _≟_

semiRing-D : SemiRing D
semiRing-D = record { _+_ = _+ᴰ_ ; _*_ = _*ᴰ_ ; 0# = 0ᴰ ; 1# = 1ᴰ ; fromℕ = fromℕ }

ring-D : Ring D
ring-D = record { sra = semiRing-D ; -_ = -ᴰ_ }

adjoint-D : Adjoint D
adjoint-D = record { adj = adjᴰ }

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_ adjᴰ

  -- Conjugation is an involutive ring automorphism (the identity).
  adj-D : IsInvolutiveRingEndo {{ring-D}} adjᴰ
  adj-D = adj-DRootTwo

  adjᴰ-id : ∀ x → adjᴰ x ≡ x
  adjᴰ-id (RootTwo a b) = refl

instance
  SemiRingD : SemiRing D
  SemiRingD = semiRing-D

  RingD : Ring D
  RingD = ring-D

  AdjointD : Adjoint D
  AdjointD = adjoint-D
