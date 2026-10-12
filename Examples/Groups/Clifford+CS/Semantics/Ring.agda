------------------------------------------------------------------------
-- Presentations of groups
--
-- The coefficient ring of the Clifford+CS semantics: the Gaussian
-- integers ℤ[i]
--
-- A Clifford+CS circuit denotes a unitary matrix with entries in
-- 𝔻[i] = ℤ[½,i].  Every gate matrix is γ⁻¹ times a matrix over ℤ[i],
-- where γ = 1 + i (so γ⁻¹ = (1 − i)/2), and a circuit of ℓ gates
-- denotes γ^(−ℓ) times a matrix over ℤ[i].  The semantics keeps the two
-- apart: the entries live in ℤ[i], represented as pairs of integers with
-- PROPOSITIONAL equality, and the power of γ⁻¹ is carried alongside
-- (Semantics.Scaled).  That is the localisation ℤ[½,i] = ℤ[i][γ⁻¹],
-- since 2 = −i γ², and it is what lets a relation between circuits be
-- checked by `refl` on stored integer matrices.
--
-- This is Real-Clifford+CH.Semantics.Ring with ℤ[√2] replaced by ℤ[i]
-- and √2 by γ: an element a + b i is the pair (a , b), and
--
--     (a + b i)(c + d i) = (ac − bd) + (ad + bc) i.
--
-- The commutative-ring laws are proved componentwise by the standard
-- library's ring solver over ℤ.  The one fact beyond the ring laws is
-- that γ is not a zero divisor, which is what makes the scaling
-- equivalence of Semantics.Scaled transitive.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Semantics.Ring where

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

infix 7 _+i_

-- a +i b is the number a + b i.  A data type rather than a record, so
-- that it has no η-rule: a product of two variables then stays inert,
-- and unification can solve for an unknown factor.
data ℤ[i] : Set where
  _+i_ : ℤ → ℤ → ℤ[i]

re im : ℤ[i] → ℤ
re (a +i b) = a
im (a +i b) = b

private
  2ℤ : ℤ
  2ℤ = + 2

------------------------------------------------------------------------
-- The operations

infixl 6 _+_ _-_
infixl 7 _*_
infix  8 -_
infixr 9 _^_

_+_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +i b) + (c +i d) = (a ℤ.+ c) +i (b ℤ.+ d)

_*_ : ℤ[i] → ℤ[i] → ℤ[i]
(a +i b) * (c +i d) =
  (a ℤ.* c ℤ.+ ℤ.- (b ℤ.* d)) +i (a ℤ.* d ℤ.+ b ℤ.* c)

-_ : ℤ[i] → ℤ[i]
- (a +i b) = (ℤ.- a) +i (ℤ.- b)

_-_ : ℤ[i] → ℤ[i] → ℤ[i]
x - y = x + - y

-- The constants: 0, ±1, ±i, γ = 1 + i, and γ i = −1 + i.
0# 1# -1# ⅈ -ⅈ γ γⅈ : ℤ[i]
0#  = 0ℤ +i 0ℤ
1#  = 1ℤ +i 0ℤ
-1# = -1ℤ +i 0ℤ
ⅈ   = 0ℤ +i 1ℤ
-ⅈ  = 0ℤ +i -1ℤ
γ   = 1ℤ +i 1ℤ
γⅈ  = -1ℤ +i 1ℤ

-- Powers.
_^_ : ℤ[i] → ℕ → ℤ[i]
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Forcing a value
--
-- The constructor is lazy in its two integers, so a number produced by
-- a long computation is, until someone looks at it, the expression
-- that produced it.  `strict` evaluates both components to literals
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

strict : ℤ[i] → ℤ[i]
strict (a +i b) = seqℤ a (seqℤ b (a +i b))

strict-id : ∀ x → strict x ≡ x
strict-id (a +i b) = Eq.trans (seqℤ-id a _) (seqℤ-id b _)

------------------------------------------------------------------------
-- Powers of γ
--
-- Evaluated strictly, one level at a time, as Real-Clifford+CH does
-- for √2: the lazy power unfolds to a tree of size 2ⁿ under the
-- conversion checker.

infix 9 γ^_

γ^_ : ℕ → ℤ[i]
γ^ zero  = 1#
γ^ suc n = strict (γ * γ^ n)

γ^-def : ∀ n → γ^ n ≡ γ ^ n
γ^-def zero    = refl
γ^-def (suc n) = Eq.trans (strict-id (γ * γ^ n)) (Eq.cong (γ *_) (γ^-def n))

------------------------------------------------------------------------
-- Decidable equality

_≟_ : DecidableEquality ℤ[i]
(a +i b) ≟ (c +i d) with a ℤ.≟ c | b ℤ.≟ d
... | yes refl | yes refl = yes refl
... | no  a≢c  | _        = no (λ e → a≢c (Eq.cong re e))
... | _        | no b≢d   = no (λ e → b≢d (Eq.cong im e))

------------------------------------------------------------------------
-- The ring laws, componentwise by the ring solver over ℤ

private
  ℤ-ring = fromCommutativeRing ℤP.+-*-commutativeRing (λ x → dec⇒maybe (0ℤ ℤ.≟ x))
  module Sol = NR ℤ-ring
  open Sol using (solve ; Κ ; _⊕_ ; _⊗_ ; ⊝_)

  ⟨_,_⟩ : ∀ {x y : ℤ[i]} → re x ≡ re y → im x ≡ im y → x ≡ y
  ⟨_,_⟩ {a +i b} {c +i d} refl refl = refl

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc (a +i b) (c +i d) (e +i f) =
  ⟨ ℤP.+-assoc a c e , ℤP.+-assoc b d f ⟩

+-comm : ∀ x y → x + y ≡ y + x
+-comm (a +i b) (c +i d) = ⟨ ℤP.+-comm a c , ℤP.+-comm b d ⟩

+-identityˡ : ∀ x → 0# + x ≡ x
+-identityˡ (a +i b) = ⟨ ℤP.+-identityˡ a , ℤP.+-identityˡ b ⟩

+-identityʳ : ∀ x → x + 0# ≡ x
+-identityʳ (a +i b) = ⟨ ℤP.+-identityʳ a , ℤP.+-identityʳ b ⟩

+-inverseˡ : ∀ x → - x + x ≡ 0#
+-inverseˡ (a +i b) = ⟨ ℤP.+-inverseˡ a , ℤP.+-inverseˡ b ⟩

+-inverseʳ : ∀ x → x + - x ≡ 0#
+-inverseʳ (a +i b) = ⟨ ℤP.+-inverseʳ a , ℤP.+-inverseʳ b ⟩

*-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
*-assoc (a +i b) (c +i d) (e +i f) = ⟨ re-eq a b c d e f , im-eq a b c d e f ⟩
  where
  re-eq = solve 6 (λ a b c d e f →
    ((a ⊗ c ⊕ ⊝ (b ⊗ d)) ⊗ e ⊕ ⊝ ((a ⊗ d ⊕ b ⊗ c) ⊗ f)) ,
    (a ⊗ (c ⊗ e ⊕ ⊝ (d ⊗ f)) ⊕ ⊝ (b ⊗ (c ⊗ f ⊕ d ⊗ e))))
    (λ {_} {_} {_} {_} {_} {_} → refl)
  im-eq = solve 6 (λ a b c d e f →
    ((a ⊗ c ⊕ ⊝ (b ⊗ d)) ⊗ f ⊕ (a ⊗ d ⊕ b ⊗ c) ⊗ e) ,
    (a ⊗ (c ⊗ f ⊕ d ⊗ e) ⊕ b ⊗ (c ⊗ e ⊕ ⊝ (d ⊗ f))))
    (λ {_} {_} {_} {_} {_} {_} → refl)

*-comm : ∀ x y → x * y ≡ y * x
*-comm (a +i b) (c +i d) = ⟨ re-eq a b c d , im-eq a b c d ⟩
  where
  re-eq = solve 4 (λ a b c d →
    (a ⊗ c ⊕ ⊝ (b ⊗ d)) , (c ⊗ a ⊕ ⊝ (d ⊗ b)))
    (λ {_} {_} {_} {_} → refl)
  im-eq = solve 4 (λ a b c d →
    (a ⊗ d ⊕ b ⊗ c) , (c ⊗ b ⊕ d ⊗ a))
    (λ {_} {_} {_} {_} → refl)

*-identityˡ : ∀ x → 1# * x ≡ x
*-identityˡ (a +i b) = ⟨ re-eq a b , im-eq a b ⟩
  where
  re-eq = solve 2 (λ a b → (Κ 1ℤ ⊗ a ⊕ ⊝ (Κ 0ℤ ⊗ b)) , a)
    (λ {_} {_} → refl)
  im-eq = solve 2 (λ a b → (Κ 1ℤ ⊗ b ⊕ Κ 0ℤ ⊗ a) , b)
    (λ {_} {_} → refl)

*-identityʳ : ∀ x → x * 1# ≡ x
*-identityʳ x = Eq.trans (*-comm x 1#) (*-identityˡ x)

*-zeroˡ : ∀ x → 0# * x ≡ 0#
*-zeroˡ (a +i b) = ⟨ re-eq a b , im-eq a b ⟩
  where
  re-eq = solve 2 (λ a b → (Κ 0ℤ ⊗ a ⊕ ⊝ (Κ 0ℤ ⊗ b)) , Κ 0ℤ)
    (λ {_} {_} → refl)
  im-eq = solve 2 (λ a b → (Κ 0ℤ ⊗ b ⊕ Κ 0ℤ ⊗ a) , Κ 0ℤ)
    (λ {_} {_} → refl)

*-zeroʳ : ∀ x → x * 0# ≡ 0#
*-zeroʳ x = Eq.trans (*-comm x 0#) (*-zeroˡ x)

*-distribˡ-+ : ∀ x y z → x * (y + z) ≡ x * y + x * z
*-distribˡ-+ (a +i b) (c +i d) (e +i f) = ⟨ re-eq a b c d e f , im-eq a b c d e f ⟩
  where
  re-eq = solve 6 (λ a b c d e f →
    (a ⊗ (c ⊕ e) ⊕ ⊝ (b ⊗ (d ⊕ f))) ,
    ((a ⊗ c ⊕ ⊝ (b ⊗ d)) ⊕ (a ⊗ e ⊕ ⊝ (b ⊗ f))))
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

γ^-+ : ∀ m n → γ^ (m Data.Nat.+ n) ≡ γ^ m * γ^ n
γ^-+ m n =
  Eq.trans (γ^-def (m Data.Nat.+ n))
    (Eq.trans (^-+ γ m n) (Eq.sym (Eq.cong₂ _*_ (γ^-def m) (γ^-def n))))

------------------------------------------------------------------------
-- γ is not a zero divisor
--
-- γ (a + b i) = (a − b) + (a + b) i, so cancelling γ is adding and
-- subtracting the two components and halving.

γ-cancel : ∀ x y → γ * x ≡ γ * y → x ≡ y
γ-cancel (a +i b) (c +i d) eq = ⟨ a≡c , b≡d ⟩
  where
  open Eq.≡-Reasoning
  -- The components of γ * (a +i b), normalised by the solver.
  reˡ : ∀ a b → 1ℤ ℤ.* a ℤ.+ ℤ.- (1ℤ ℤ.* b) ≡ a ℤ.+ ℤ.- b
  reˡ = solve 2 (λ a b → (Κ 1ℤ ⊗ a ⊕ ⊝ (Κ 1ℤ ⊗ b)) , (a ⊕ ⊝ b)) (λ {_} {_} → refl)
  imˡ : ∀ a b → 1ℤ ℤ.* b ℤ.+ 1ℤ ℤ.* a ≡ a ℤ.+ b
  imˡ = solve 2 (λ a b → (Κ 1ℤ ⊗ b ⊕ Κ 1ℤ ⊗ a) , (a ⊕ b)) (λ {_} {_} → refl)
  sum : ∀ a b → (a ℤ.+ ℤ.- b) ℤ.+ (a ℤ.+ b) ≡ 2ℤ ℤ.* a
  sum = solve 2 (λ a b → ((a ⊕ ⊝ b) ⊕ (a ⊕ b)) , (Κ 2ℤ ⊗ a)) (λ {_} {_} → refl)
  dif : ∀ a b → (a ℤ.+ b) ℤ.+ ℤ.- (a ℤ.+ ℤ.- b) ≡ 2ℤ ℤ.* b
  dif = solve 2 (λ a b → ((a ⊕ b) ⊕ ⊝ (a ⊕ ⊝ b)) , (Κ 2ℤ ⊗ b)) (λ {_} {_} → refl)
  r : a ℤ.+ ℤ.- b ≡ c ℤ.+ ℤ.- d
  r = Eq.trans (Eq.sym (reˡ a b)) (Eq.trans (Eq.cong re eq) (reˡ c d))
  i : a ℤ.+ b ≡ c ℤ.+ d
  i = Eq.trans (Eq.sym (imˡ a b)) (Eq.trans (Eq.cong im eq) (imˡ c d))
  a≡c : a ≡ c
  a≡c = ℤP.*-cancelˡ-≡ 2ℤ a c
          (Eq.trans (Eq.sym (sum a b)) (Eq.trans (Eq.cong₂ ℤ._+_ r i) (sum c d)))
  b≡d : b ≡ d
  b≡d = ℤP.*-cancelˡ-≡ 2ℤ b d
          (Eq.trans (Eq.sym (dif a b)) (Eq.trans (Eq.cong₂ (λ u v → u ℤ.+ ℤ.- v) i r) (dif c d)))

^-cancel : ∀ n x y → γ ^ n * x ≡ γ ^ n * y → x ≡ y
^-cancel zero    x y eq = Eq.trans (Eq.sym (*-identityˡ x)) (Eq.trans eq (*-identityˡ y))
^-cancel (suc n) x y eq =
  ^-cancel n x y
    (γ-cancel (γ ^ n * x) (γ ^ n * y)
      (Eq.trans (Eq.sym (*-assoc γ (γ ^ n) x))
        (Eq.trans eq (*-assoc γ (γ ^ n) y))))

γ^-cancel : ∀ n x y → γ^ n * x ≡ γ^ n * y → x ≡ y
γ^-cancel n x y eq = ^-cancel n x y
  (Eq.trans (Eq.cong (_* x) (Eq.sym (γ^-def n)))
    (Eq.trans eq (Eq.cong (_* y) (γ^-def n))))

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
-- A ring solver for ℤ[i] itself

module Solver where
  private
    ring = fromCommutativeRing +-*-commutativeRing (λ x → dec⇒maybe (0# ≟ x))
  open NR ring public using (solve ; Κ ; Ι ; _⊕_ ; _⊗_ ; ⊝_)
