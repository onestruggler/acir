------------------------------------------------------------------------
-- Presentations of groups
--
-- The ring 𝔻 = ℤ[1/2] of dyadic fractions (Definition 2.1), the entries
-- of the orthogonal matrices Oₙ(ℤ[1/2]), taken from EucDomain, with the
-- integers ℤ embedded (ι).
--
-- As in Real-Clifford+CH-TwoLevel.Ring, the operations of 𝔻 are opaque:
-- its elements are records with a normal form, and comparing two
-- convertible but different expressions would otherwise unfold the
-- dyadic arithmetic on stuck terms.  Computations that need the
-- arithmetic go in `opaque unfolding` blocks.  Conjugation is the
-- identity, so the unitary matrices over 𝔻 are the orthogonal ones.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec)

open import Instances
  using (_≟_ ; SemiRing ; Ring ; Adjoint ; _+_ ; _*_ ; -_ ; 0# ; 1# ; fromℕ ; adj)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; DecEqDyadic)
open import Quantum.Synthesis.Ring.Properties
  using (isCommutativeRing-𝔻 ; commutativeRing-𝔻 ; IsInvolutiveRingEndo ; adj-𝔻)
import Quantum.Synthesis.Ring.Properties.Common as Common
import Examples.Groups.Clifford+CS-TwoLevel.Algebra as Algebra

open import Examples.Groups.Clifford+CS-TwoLevel.Ring public
  using ( oddℕ ; oddℤ ; oddℤ-+ ; oddℤ-neg ; oddℤ-* ; oddℤ-double ; evenℤ-half
        ; ι₀ ; ι₀-+ ; ι₀-* ; ι₀-neg ; ι₀-injective )

------------------------------------------------------------------------
-- The ring

-- 𝔻 = ℤ[1/2], the ring of the matrix entries.
D : Set
D = Dyadic

-- The operations of 𝔻: EucDomain's, made opaque, and conjugation.
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
  isCommutativeRing-D = isCommutativeRing-𝔻

commutativeRing-D : CommutativeRing 0ℓ 0ℓ
commutativeRing-D = record { isCommutativeRing = isCommutativeRing-D }

-- The ring structures: 𝔻's opaque one, and EucDomain's.
module 𝔻R = CommutativeRing commutativeRing-𝔻
module DR = CommutativeRing commutativeRing-D

-- A ring solver with integer coefficients.
module DS = Common.ZSolver commutativeRing-D

-- Identities in 𝔻, proved over an abstract ring.
module DA = Algebra commutativeRing-D (λ p → p)

------------------------------------------------------------------------
-- Constants

-- 1/2, the scalar of K = H ⊗ H, and 2.
½ᴰ 2ᴰ : D
½ᴰ = Dyadic' (+ 1) 1 _
2ᴰ = Dyadic' (+ 2) 0 _

opaque
  unfolding _+ᴰ_ _*ᴰ_

  2*½ : 2ᴰ *ᴰ ½ᴰ ≡ 1ᴰ
  2*½ = refl

  ½*2 : ½ᴰ *ᴰ 2ᴰ ≡ 1ᴰ
  ½*2 = refl

  -- 4 (1/2)² = 1.
  ½-quarter : ½ᴰ *ᴰ ½ᴰ +ᴰ ½ᴰ *ᴰ ½ᴰ +ᴰ ½ᴰ *ᴰ ½ᴰ +ᴰ ½ᴰ *ᴰ ½ᴰ ≡ 1ᴰ
  ½-quarter = refl

------------------------------------------------------------------------
-- The embedding ℤ → 𝔻

ι : ℤ → D
ι = ι₀

ι-injective : ∀ {a b} → ι a ≡ ι b → a ≡ b
ι-injective = ι₀-injective

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  ι-+ : ∀ a b → ι (a ℤ.+ b) ≡ ι a DR.+ ι b
  ι-+ = ι₀-+

  ι-* : ∀ a b → ι (a ℤ.* b) ≡ ι a DR.* ι b
  ι-* = ι₀-*

  ι-neg : ∀ a → ι (ℤ.- a) ≡ DR.- ι a
  ι-neg = ι₀-neg

ι-0 : ι (+ 0) ≡ DR.0#
ι-0 = refl

ι-1 : ι (+ 1) ≡ DR.1#
ι-1 = refl

ι-2 : ι (+ 2) ≡ 2ᴰ
ι-2 = refl

------------------------------------------------------------------------
-- Instances

-- Decidable equality.
infix 4 _≟ᴰ_

_≟ᴰ_ : (x y : D) → Dec (x ≡ y)
_≟ᴰ_ = _≟_

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
  adj-D = adj-𝔻

  adjᴰ-id : ∀ x → adjᴰ x ≡ x
  adjᴰ-id x = refl

instance
  SemiRingD : SemiRing D
  SemiRingD = semiRing-D

  RingD : Ring D
  RingD = ring-D

  AdjointD : Adjoint D
  AdjointD = adjoint-D
