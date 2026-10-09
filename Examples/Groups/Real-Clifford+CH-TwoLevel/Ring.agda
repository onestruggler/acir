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
open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Solver as ℤSolver
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _,_)
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
open import Algebra.Solver.Ring.AlmostCommutativeRing using (fromCommutativeRing)
import Algebra.Solver.Ring.Simple
import Examples.Groups.Clifford+CS-TwoLevel.Algebra as Algebra

open import Examples.Groups.Clifford+CS-TwoLevel.Ring public
  using ( oddℕ ; oddℤ ; oddℤ-+ ; oddℤ-neg ; oddℤ-* ; oddℤ-double ; evenℤ-half
        ; ι₀ ; ι₀-+ ; ι₀-* ; ι₀-neg ; ι₀-injective )

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

-- A ring solver over ℤ[√2] with coefficients in ℤ[√2]: constants such
-- as √2 multiply out by computation.
module ZG = Algebra.Solver.Ring.Simple (fromCommutativeRing commutativeRing-ZRootTwo) (λ x y → x ≟ y)

-- Identities in 𝔻[√2], proved over an abstract ring.
module DA = Algebra commutativeRing-D (λ p → p)

private
  module ℤS = ℤSolver.+-*-Solver

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

-- √2, in both rings.
√2ᴰ : D
√2ᴰ = RootTwo d0 d1

√2ᶻ : Z
√2ᶻ = RootTwo (+ 0) (+ 1)

opaque
  unfolding _*ᴰ_

  √2*√½ : √2ᴰ *ᴰ √½ ≡ 1ᴰ
  √2*√½ = refl

  √½*√2 : √½ *ᴰ √2ᴰ ≡ 1ᴰ
  √½*√2 = refl

------------------------------------------------------------------------
-- Powers
--
-- EucDomain's _^_ computes by repeated squaring; for reasoning we use
-- the naive power.

infixr 8 _^ᴰ_ _^ᶻ_

_^ᴰ_ : D → ℕ → D
_^ᴰ_ = DA._^_

_^ᶻ_ : Z → ℕ → Z
x ^ᶻ zero  = ZR.1#
x ^ᶻ suc k = x ZR.* (x ^ᶻ k)

^ᶻ-+ : ∀ x m n → x ^ᶻ (m ℕ.+ n) ≡ (x ^ᶻ m) ZR.* (x ^ᶻ n)
^ᶻ-+ x zero n = sym (ZR.*-identityˡ _)
^ᶻ-+ x (suc m) n = trans (cong (x ZR.*_) (^ᶻ-+ x m n)) (sym (ZR.*-assoc x (x ^ᶻ m) (x ^ᶻ n)))

------------------------------------------------------------------------
-- The embedding ℤ[√2] → 𝔻[√2]

emb : Z → D
emb (RootTwo a b) = RootTwo (ι₀ a) (ι₀ b)

emb-injective : ∀ {x y} → emb x ≡ emb y → x ≡ y
emb-injective {RootTwo a b} {RootTwo c d} eq =
  cong₂ RootTwo (ι₀-injective (cong ra eq)) (ι₀-injective (cong rb eq))
  where
  ra rb : D → Dyadic
  ra (RootTwo u _) = u
  rb (RootTwo _ v) = v

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  emb-+ : ∀ x y → emb (x ZR.+ y) ≡ emb x DR.+ emb y
  emb-+ (RootTwo a b) (RootTwo c d) = cong₂ RootTwo (ι₀-+ a c) (ι₀-+ b d)

  emb-neg : ∀ x → emb (ZR.- x) ≡ DR.- emb x
  emb-neg (RootTwo a b) = cong₂ RootTwo (ι₀-neg a) (ι₀-neg b)

  emb-* : ∀ x y → emb (x ZR.* y) ≡ emb x DR.* emb y
  emb-* (RootTwo a b) (RootTwo c d) = cong₂ RootTwo
    (trans (ι₀-+ (a ℤ.* c) (b ℤ.* d ℤ.+ b ℤ.* d))
           (cong₂ 𝔻R._+_ (ι₀-* a c) (trans (ι₀-+ (b ℤ.* d) (b ℤ.* d)) (cong₂ 𝔻R._+_ (ι₀-* b d) (ι₀-* b d)))))
    (trans (ι₀-+ (a ℤ.* d) (c ℤ.* b)) (cong₂ 𝔻R._+_ (ι₀-* a d) (ι₀-* c b)))

emb-0 : emb ZR.0# ≡ DR.0#
emb-0 = refl

emb-1 : emb ZR.1# ≡ DR.1#
emb-1 = refl

emb-√2 : emb √2ᶻ ≡ √2ᴰ
emb-√2 = refl

emb-^ : ∀ x k → emb (x ^ᶻ k) ≡ emb x ^ᴰ k
emb-^ x zero = refl
emb-^ x (suc k) = trans (emb-* x (x ^ᶻ k)) (cong (emb x DR.*_) (emb-^ x k))

------------------------------------------------------------------------
-- Parity: the residue modulo √2
--
-- a + b√2 ≡ a (mod √2), so it is odd (a unit modulo √2) iff a is odd.

oddᶻ : Z → Bool
oddᶻ (RootTwo a b) = oddℤ a

private
  xor-false : ∀ b → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

-- Parity is a ring homomorphism ℤ[√2] → 𝔽₂ (with xor as addition).
oddᶻ-+ : ∀ x y → oddᶻ (x ZR.+ y) ≡ oddᶻ x xor oddᶻ y
oddᶻ-+ (RootTwo a b) (RootTwo c d) = oddℤ-+ a c

oddᶻ-neg : ∀ x → oddᶻ (ZR.- x) ≡ oddᶻ x
oddᶻ-neg (RootTwo a b) = oddℤ-neg a

oddᶻ-* : ∀ x y → oddᶻ (x ZR.* y) ≡ oddᶻ x ∧ oddᶻ y
oddᶻ-* (RootTwo a b) (RootTwo c d) =
  trans (oddℤ-+ (a ℤ.* c) (b ℤ.* d ℤ.+ b ℤ.* d))
        (trans (cong₂ _xor_ (oddℤ-* a c) (oddℤ-double (b ℤ.* d))) (xor-false _))

oddᶻ-√2 : oddᶻ √2ᶻ ≡ false
oddᶻ-√2 = refl

oddᶻ-1 : oddᶻ ZR.1# ≡ true
oddᶻ-1 = refl

oddᶻ-0 : oddᶻ ZR.0# ≡ false
oddᶻ-0 = refl

-- The second residue bit: an odd element is ≡ 1 or ≡ 1 + √2 (mod 2)
-- according to the parity of its √2-coefficient.
rbit : Z → Bool
rbit (RootTwo a b) = oddℤ b

rbit-+ : ∀ x y → rbit (x ZR.+ y) ≡ rbit x xor rbit y
rbit-+ (RootTwo a b) (RootTwo c d) = oddℤ-+ b d

rbit-neg : ∀ x → rbit (ZR.- x) ≡ rbit x
rbit-neg (RootTwo a b) = oddℤ-neg b

------------------------------------------------------------------------
-- Divisibility by √2

infix 4 δ∣_

δ∣_ : Z → Set
δ∣ w = ∃ λ y → w ≡ √2ᶻ ZR.* y

-- √2 (p + q√2) = 2q + p√2.
√2*≡ : ∀ p q → √2ᶻ ZR.* RootTwo p q ≡ RootTwo (q ℤ.+ q) p
√2*≡ p q = cong₂ RootTwo
  (ℤS.solve 2 (λ p q → con (+ 0) :* p :+ (con (+ 1) :* q :+ con (+ 1) :* q) := q :+ q) refl p q)
  (ℤS.solve 2 (λ p q → con (+ 0) :* q :+ p :* con (+ 1) := p) refl p q)
  where open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)

-- An element of ℤ[√2] is even iff it is divisible by √2.
δ∣⇒even : ∀ {w} → δ∣ w → oddᶻ w ≡ false
δ∣⇒even {w} (y , refl) = oddᶻ-* √2ᶻ y

even⇒δ∣ : ∀ w → oddᶻ w ≡ false → δ∣ w
even⇒δ∣ (RootTwo a b) e with evenℤ-half a e
... | s , p = RootTwo b s , trans (cong (λ x → RootTwo x b) p) (sym (√2*≡ b s))

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
