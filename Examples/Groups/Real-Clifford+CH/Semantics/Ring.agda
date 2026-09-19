------------------------------------------------------------------------
-- Presentations of groups
--
-- The coefficient ring of the real-Clifford+CH semantics: ℤ[√2]
--
-- A real-Clifford+CH circuit denotes a real matrix with entries in
-- ℤ[1/√2] (Clément, Definition 2.3).  Every gate matrix is (1/√2) times
-- a matrix over ℤ[√2], so a circuit of ℓ gates denotes (1/√2)^ℓ times a
-- matrix over ℤ[√2].  The semantics keeps the two apart: the entries
-- live in ℤ[√2], represented as pairs of integers with PROPOSITIONAL
-- equality, and the power of 1/√2 is carried alongside (Semantics.
-- Scaled).  That is the localisation ℤ[1/√2] = ℤ[√2][1/√2], and it is
-- what lets a relation between circuits be checked by `refl` on stored
-- integer matrices, where rationals would have to be normalised at
-- every step.
--
-- An element a + b√2 is the pair (a , b); the product is
--
--     (a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2.
--
-- The commutative-ring laws are proved componentwise by the standard
-- library's ring solver over ℤ.  Only what the operator algebra needs
-- is exported by name; the whole structure is also bundled.  The one
-- fact beyond the ring laws is that √2 is not a zero divisor, which is
-- what makes the scaling equivalence of Semantics.Scaled transitive.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Integer as ℤ using (ℤ ; 0ℤ ; 1ℤ ; -1ℤ ; +_ ; -[1+_])
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (yes ; no ; dec⇒maybe)
open import Tactic.RingSolver.Core.AlmostCommutativeRing
  using (fromCommutativeRing)

import Data.Integer.Properties as ℤP
import Tactic.RingSolver.NonReflective as NR

------------------------------------------------------------------------
-- The carrier

infix 7 _+√2_

-- a +√2 b is the number a + b√2.  A data type rather than a record, so
-- that it has no η-rule: a product of two variables then stays inert,
-- and unification can solve for an unknown factor.
data ℤ√2 : Set where
  _+√2_ : ℤ → ℤ → ℤ√2

re im : ℤ√2 → ℤ
re (a +√2 b) = a
im (a +√2 b) = b

private
  2ℤ : ℤ
  2ℤ = + 2

------------------------------------------------------------------------
-- The operations

infixl 6 _+_ _-_
infixl 7 _*_
infix  8 -_
infixr 9 _^_

_+_ : ℤ√2 → ℤ√2 → ℤ√2
(a +√2 b) + (c +√2 d) = (a ℤ.+ c) +√2 (b ℤ.+ d)

_*_ : ℤ√2 → ℤ√2 → ℤ√2
(a +√2 b) * (c +√2 d) =
  (a ℤ.* c ℤ.+ 2ℤ ℤ.* (b ℤ.* d)) +√2 (a ℤ.* d ℤ.+ b ℤ.* c)

-_ : ℤ√2 → ℤ√2
- (a +√2 b) = (ℤ.- a) +√2 (ℤ.- b)

_-_ : ℤ√2 → ℤ√2 → ℤ√2
x - y = x + - y

0# 1# -1# √2 -√2 : ℤ√2
0#  = 0ℤ +√2 0ℤ
1#  = 1ℤ +√2 0ℤ
-1# = -1ℤ +√2 0ℤ
√2  = 0ℤ +√2 1ℤ
-√2 = 0ℤ +√2 -1ℤ

-- Powers, and the powers of √2 that scale a circuit's matrix.
_^_ : ℤ√2 → ℕ → ℤ√2
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Forcing a value
--
-- The constructor is lazy in its two integers, so a number produced by
-- a long computation is, until someone looks at it, the expression
-- that produced it — and inside a stored matrix those expressions are
-- duplicated by every product that reads the entry, and grow without
-- bound.  `strict` looks: it evaluates both components to literals
-- before rebuilding the pair, and is the identity.  Algebra.matOf
-- applies it to every entry it stores.

private
  seqℕ : {A : Set} → ℕ → A → A
  seqℕ zero    a = a
  seqℕ (suc _) a = a

  seqℤ : {A : Set} → ℤ → A → A
  seqℤ (+ n)      a = seqℕ n a
  seqℤ (-[1+ n ]) a = seqℕ n a

  seqℕ-id : {A : Set} (n : ℕ) (a : A) → seqℕ n a ≡ a
  seqℕ-id zero    a = refl
  seqℕ-id (suc _) a = refl

  seqℤ-id : {A : Set} (z : ℤ) (a : A) → seqℤ z a ≡ a
  seqℤ-id (+ n)      a = seqℕ-id n a
  seqℤ-id (-[1+ n ]) a = seqℕ-id n a

strict : ℤ√2 → ℤ√2
strict (a +√2 b) = seqℤ a (seqℤ b (a +√2 b))

strict-id : ∀ x → strict x ≡ x
strict-id (a +√2 b) = Eq.trans (seqℤ-id a _) (seqℤ-id b _)

------------------------------------------------------------------------
-- Powers of √2
--
-- Evaluated strictly, one level at a time.  √2 ^ n unfolds to a
-- product each of whose lazy components mentions both components of
-- the level below, so a closed power that the conversion checker
-- happens to evaluate — the scalar of an eighty-letter relator, say —
-- is to it a tree of size 2ⁿ, and the checker runs out of memory on
-- √2 ^ 27.  Forcing every level keeps each a pair of literals.  The
-- facts used downstream, that powers add and that a power cancels, come
-- from the lazy power through √2^-def.

infix 9 √2^_

√2^_ : ℕ → ℤ√2
√2^ zero  = 1#
√2^ suc n = strict (√2 * √2^ n)

√2^-def : ∀ n → √2^ n ≡ √2 ^ n
√2^-def zero    = refl
√2^-def (suc n) = Eq.trans (strict-id (√2 * √2^ n)) (Eq.cong (√2 *_) (√2^-def n))

------------------------------------------------------------------------
-- Decidable equality

_≟_ : DecidableEquality ℤ√2
(a +√2 b) ≟ (c +√2 d) with a ℤ.≟ c | b ℤ.≟ d
... | yes refl | yes refl = yes refl
... | no  a≢c  | _        = no (λ e → a≢c (Eq.cong re e))
... | _        | no b≢d   = no (λ e → b≢d (Eq.cong im e))

------------------------------------------------------------------------
-- The ring laws, componentwise by the ring solver over ℤ

private
  ℤ-ring = fromCommutativeRing ℤP.+-*-commutativeRing (λ x → dec⇒maybe (0ℤ ℤ.≟ x))
  module Sol = NR ℤ-ring
  open Sol using (solve ; Κ ; _⊕_ ; _⊗_ ; ⊝_)

  ⟨_,_⟩ : ∀ {x y : ℤ√2} → re x ≡ re y → im x ≡ im y → x ≡ y
  ⟨_,_⟩ {a +√2 b} {c +√2 d} refl refl = refl

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc (a +√2 b) (c +√2 d) (e +√2 f) =
  ⟨ ℤP.+-assoc a c e , ℤP.+-assoc b d f ⟩

+-comm : ∀ x y → x + y ≡ y + x
+-comm (a +√2 b) (c +√2 d) = ⟨ ℤP.+-comm a c , ℤP.+-comm b d ⟩

+-identityˡ : ∀ x → 0# + x ≡ x
+-identityˡ (a +√2 b) = ⟨ ℤP.+-identityˡ a , ℤP.+-identityˡ b ⟩

+-identityʳ : ∀ x → x + 0# ≡ x
+-identityʳ (a +√2 b) = ⟨ ℤP.+-identityʳ a , ℤP.+-identityʳ b ⟩

+-inverseˡ : ∀ x → - x + x ≡ 0#
+-inverseˡ (a +√2 b) = ⟨ ℤP.+-inverseˡ a , ℤP.+-inverseˡ b ⟩

+-inverseʳ : ∀ x → x + - x ≡ 0#
+-inverseʳ (a +√2 b) = ⟨ ℤP.+-inverseʳ a , ℤP.+-inverseʳ b ⟩

*-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
*-assoc (a +√2 b) (c +√2 d) (e +√2 f) = ⟨ re-eq a b c d e f , im-eq a b c d e f ⟩
  where
  re-eq = solve 6 (λ a b c d e f →
    ((a ⊗ c ⊕ Κ 2ℤ ⊗ (b ⊗ d)) ⊗ e ⊕ Κ 2ℤ ⊗ ((a ⊗ d ⊕ b ⊗ c) ⊗ f)) ,
    (a ⊗ (c ⊗ e ⊕ Κ 2ℤ ⊗ (d ⊗ f)) ⊕ Κ 2ℤ ⊗ (b ⊗ (c ⊗ f ⊕ d ⊗ e))))
    (λ {_} {_} {_} {_} {_} {_} → refl)
  im-eq = solve 6 (λ a b c d e f →
    ((a ⊗ c ⊕ Κ 2ℤ ⊗ (b ⊗ d)) ⊗ f ⊕ (a ⊗ d ⊕ b ⊗ c) ⊗ e) ,
    (a ⊗ (c ⊗ f ⊕ d ⊗ e) ⊕ b ⊗ (c ⊗ e ⊕ Κ 2ℤ ⊗ (d ⊗ f))))
    (λ {_} {_} {_} {_} {_} {_} → refl)

*-comm : ∀ x y → x * y ≡ y * x
*-comm (a +√2 b) (c +√2 d) = ⟨ re-eq a b c d , im-eq a b c d ⟩
  where
  re-eq = solve 4 (λ a b c d →
    (a ⊗ c ⊕ Κ 2ℤ ⊗ (b ⊗ d)) , (c ⊗ a ⊕ Κ 2ℤ ⊗ (d ⊗ b)))
    (λ {_} {_} {_} {_} → refl)
  im-eq = solve 4 (λ a b c d →
    (a ⊗ d ⊕ b ⊗ c) , (c ⊗ b ⊕ d ⊗ a))
    (λ {_} {_} {_} {_} → refl)

*-identityˡ : ∀ x → 1# * x ≡ x
*-identityˡ (a +√2 b) = ⟨ re-eq a b , im-eq a b ⟩
  where
  re-eq = solve 2 (λ a b → (Κ 1ℤ ⊗ a ⊕ Κ 2ℤ ⊗ (Κ 0ℤ ⊗ b)) , a)
    (λ {_} {_} → refl)
  im-eq = solve 2 (λ a b → (Κ 1ℤ ⊗ b ⊕ Κ 0ℤ ⊗ a) , b)
    (λ {_} {_} → refl)

*-identityʳ : ∀ x → x * 1# ≡ x
*-identityʳ x = Eq.trans (*-comm x 1#) (*-identityˡ x)

*-zeroˡ : ∀ x → 0# * x ≡ 0#
*-zeroˡ (a +√2 b) = ⟨ re-eq a b , im-eq a b ⟩
  where
  re-eq = solve 2 (λ a b → (Κ 0ℤ ⊗ a ⊕ Κ 2ℤ ⊗ (Κ 0ℤ ⊗ b)) , Κ 0ℤ)
    (λ {_} {_} → refl)
  im-eq = solve 2 (λ a b → (Κ 0ℤ ⊗ b ⊕ Κ 0ℤ ⊗ a) , Κ 0ℤ)
    (λ {_} {_} → refl)

*-zeroʳ : ∀ x → x * 0# ≡ 0#
*-zeroʳ x = Eq.trans (*-comm x 0#) (*-zeroˡ x)

*-distribˡ-+ : ∀ x y z → x * (y + z) ≡ x * y + x * z
*-distribˡ-+ (a +√2 b) (c +√2 d) (e +√2 f) = ⟨ re-eq a b c d e f , im-eq a b c d e f ⟩
  where
  re-eq = solve 6 (λ a b c d e f →
    (a ⊗ (c ⊕ e) ⊕ Κ 2ℤ ⊗ (b ⊗ (d ⊕ f))) ,
    ((a ⊗ c ⊕ Κ 2ℤ ⊗ (b ⊗ d)) ⊕ (a ⊗ e ⊕ Κ 2ℤ ⊗ (b ⊗ f))))
    (λ {_} {_} {_} {_} {_} {_} → refl)
  im-eq = solve 6 (λ a b c d e f →
    (a ⊗ (d ⊕ f) ⊕ b ⊗ (c ⊕ e)) ,
    ((a ⊗ d ⊕ b ⊗ c) ⊕ (a ⊗ f ⊕ b ⊗ e)))
    (λ {_} {_} {_} {_} {_} {_} → refl)

*-distribʳ-+ : ∀ x y z → (y + z) * x ≡ y * x + z * x
*-distribʳ-+ x y z =
  Eq.trans (*-comm (y + z) x)
    (Eq.trans (*-distribˡ-+ x y z) (Eq.cong₂ _+_ (*-comm x y) (*-comm x z)))

-‿cong : ∀ {x y} → x ≡ y → - x ≡ - y
-‿cong refl = refl

------------------------------------------------------------------------
-- Two four-term rearrangements the operator algebra uses

+-shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle a b c d = begin
  (a + b) + (c + d)   ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))   ≡⟨ Eq.cong (λ □ → a + □) (Eq.sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)   ≡⟨ Eq.cong (λ □ → a + (□ + d)) (+-comm b c) ⟩
  a + ((c + b) + d)   ≡⟨ Eq.cong (λ □ → a + □) (+-assoc c b d) ⟩
  a + (c + (b + d))   ≡⟨ Eq.sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d)   ∎
  where open Eq.≡-Reasoning

*-cross : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
*-cross a b c d = begin
  (a * b) * (c * d)   ≡⟨ *-assoc a b (c * d) ⟩
  a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (*-assoc b c d)) ⟩
  a * ((b * c) * d)   ≡⟨ Eq.cong (λ □ → a * (□ * d)) (*-comm b c) ⟩
  a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (*-assoc c b d) ⟩
  a * (c * (b * d))   ≡⟨ Eq.sym (*-assoc a c (b * d)) ⟩
  (a * c) * (b * d)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Powers

^-+ : ∀ x m n → x ^ (m Data.Nat.+ n) ≡ x ^ m * x ^ n
^-+ x zero    n = Eq.sym (*-identityˡ (x ^ n))
^-+ x (suc m) n = Eq.trans (Eq.cong (x *_) (^-+ x m n)) (Eq.sym (*-assoc x (x ^ m) (x ^ n)))

√2^-+ : ∀ m n → √2^ (m Data.Nat.+ n) ≡ √2^ m * √2^ n
√2^-+ m n =
  Eq.trans (√2^-def (m Data.Nat.+ n))
    (Eq.trans (^-+ √2 m n) (Eq.sym (Eq.cong₂ _*_ (√2^-def m) (√2^-def n))))

------------------------------------------------------------------------
-- √2 is not a zero divisor
--
-- √2 (a + b√2) = 2b + a√2, so cancelling √2 is reading off a and
-- halving 2b.

√2-cancel : ∀ x y → √2 * x ≡ √2 * y → x ≡ y
√2-cancel (a +√2 b) (c +√2 d) eq = ⟨ a≡c , b≡d ⟩
  where
  open Eq.≡-Reasoning
  -- The components of √2 * (a +√2 b), normalised by the solver.
  reˡ : ∀ a b → 0ℤ ℤ.* a ℤ.+ 2ℤ ℤ.* (1ℤ ℤ.* b) ≡ 2ℤ ℤ.* b
  reˡ = solve 2 (λ a b → (Κ 0ℤ ⊗ a ⊕ Κ 2ℤ ⊗ (Κ 1ℤ ⊗ b)) , Κ 2ℤ ⊗ b) (λ {_} {_} → refl)
  imˡ : ∀ a b → 0ℤ ℤ.* b ℤ.+ 1ℤ ℤ.* a ≡ a
  imˡ = solve 2 (λ a b → (Κ 0ℤ ⊗ b ⊕ Κ 1ℤ ⊗ a) , a) (λ {_} {_} → refl)
  a≡c : a ≡ c
  a≡c = Eq.trans (Eq.sym (imˡ a b)) (Eq.trans (Eq.cong im eq) (imˡ c d))
  2b≡2d : 2ℤ ℤ.* b ≡ 2ℤ ℤ.* d
  2b≡2d = Eq.trans (Eq.sym (reˡ a b)) (Eq.trans (Eq.cong re eq) (reˡ c d))
  b≡d : b ≡ d
  b≡d = ℤP.*-cancelˡ-≡ 2ℤ b d 2b≡2d

^-cancel : ∀ n x y → √2 ^ n * x ≡ √2 ^ n * y → x ≡ y
^-cancel zero    x y eq = Eq.trans (Eq.sym (*-identityˡ x)) (Eq.trans eq (*-identityˡ y))
^-cancel (suc n) x y eq =
  ^-cancel n x y
    (√2-cancel (√2 ^ n * x) (√2 ^ n * y)
      (Eq.trans (Eq.sym (*-assoc √2 (√2 ^ n) x))
        (Eq.trans eq (*-assoc √2 (√2 ^ n) y))))

√2^-cancel : ∀ n x y → √2^ n * x ≡ √2^ n * y → x ≡ y
√2^-cancel n x y eq = ^-cancel n x y
  (Eq.trans (Eq.cong (_* x) (Eq.sym (√2^-def n)))
    (Eq.trans eq (Eq.cong (_* y) (√2^-def n))))

------------------------------------------------------------------------
-- The bundled structure

+-*-isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1#
+-*-isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = Eq.isEquivalence
              ; ∙-cong        = Eq.cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity = +-identityˡ , +-identityʳ
          }
        ; inverse = +-inverseˡ , +-inverseʳ
        ; ⁻¹-cong = -‿cong
        }
      ; comm = +-comm
      }
    ; *-cong     = Eq.cong₂ _*_
    ; *-assoc    = *-assoc
    ; *-identity = *-identityˡ , *-identityʳ
    ; distrib    = *-distribˡ-+ , *-distribʳ-+
    }
  ; *-comm = *-comm
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record { isCommutativeRing = +-*-isCommutativeRing }

------------------------------------------------------------------------
-- A ring solver for ℤ[√2] itself

module Solver where
  private
    ring = fromCommutativeRing +-*-commutativeRing (λ x → dec⇒maybe (0# ≟ x))
  open NR ring public using (solve ; Κ ; Ι ; _⊕_ ; _⊗_ ; ⊝_)
