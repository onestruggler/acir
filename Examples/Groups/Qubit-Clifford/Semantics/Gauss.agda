------------------------------------------------------------------------
-- Presentations of groups
--
-- Gaussian integers, the coefficients of the Clifford gates once the
-- factors 1/√2 are taken out, and their image in a commutative ring
-- with an element i such that i i = −1
--
-- The gates are checked on matrices over ℤ[i] by evaluation, so the
-- operations are plain functions on pairs of integers, with a decidable
-- equality; ι sends a + b i to a + i b and is a ring homomorphism.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Semantics.Gauss where

open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)

------------------------------------------------------------------------
-- Gaussian integers

infix 5 _+i_
record ℤi : Set where
  constructor _+i_
  field
    re im : ℤ

open ℤi public

infixl 6 _+ᵍ_
infixl 7 _*ᵍ_

_+ᵍ_ _*ᵍ_ : ℤi → ℤi → ℤi
(a +i b) +ᵍ (c +i d) = (a ℤ.+ c) +i (b ℤ.+ d)
(a +i b) *ᵍ (c +i d) = (a ℤ.* c ℤ.- b ℤ.* d) +i (a ℤ.* d ℤ.+ b ℤ.* c)

0ᵍ 1ᵍ iᵍ : ℤi
0ᵍ = + 0 +i + 0
1ᵍ = + 1 +i + 0
iᵍ = + 0 +i + 1

-- Multiplication by 2, and complex conjugation.
dblᵍ conjᵍ : ℤi → ℤi
dblᵍ (a +i b)  = (+ 2 ℤ.* a) +i (+ 2 ℤ.* b)
conjᵍ (a +i b) = a +i ℤ.- b

infix 4 _≟ᵍ_
_≟ᵍ_ : DecidableEquality ℤi
(a +i b) ≟ᵍ (c +i d) with a ℤP.≟ c | b ℤP.≟ d
... | yes Eq.refl | yes Eq.refl = yes Eq.refl
... | no a≢c      | _           = no λ e → a≢c (Eq.cong re e)
... | yes _       | no b≢d      = no λ e → b≢d (Eq.cong im e)

------------------------------------------------------------------------
-- The image in a commutative ring with i i = −1

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)
import Quantum.Synthesis.Ring.Properties.Common as Common

module Image
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (i : A) (i² : i * i ≡ - 1#)
  where

  private
    R : CommutativeRing _ _
    R = record { isCommutativeRing = isCR }
    module AR = CommutativeRing R

  module ZS = Common.ZSolver R
  open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; _:-_ ; :-_ ; con)

  ι : ℤ → A
  ι = ZS.⟦_⟧ℤ

  ιᵍ : ℤi → A
  ιᵍ (a +i b) = ι a + i * ι b

  ι-- : (a b : ℤ) → ι (a ℤ.- b) ≡ ι a + - ι b
  ι-- a b = Eq.trans (ZS.+-homoℤ a (ℤ.- b)) (Eq.cong (λ u → ι a + u) (ZS.-‿homoℤ b))

  ιᵍ-+ : (x y : ℤi) → ιᵍ (x +ᵍ y) ≡ ιᵍ x + ιᵍ y
  ιᵍ-+ (a +i b) (c +i d) = begin
    ι (a ℤ.+ c) + i * ι (b ℤ.+ d)        ≡⟨ Eq.cong₂ (λ u v → u + i * v) (ZS.+-homoℤ a c) (ZS.+-homoℤ b d) ⟩
    (ι a + ι c) + i * (ι b + ι d)        ≡⟨ solve 5 (λ a b c d i → (a :+ c) :+ i :* (b :+ d) := (a :+ i :* b) :+ (c :+ i :* d))
                                               Eq.refl (ι a) (ι b) (ι c) (ι d) i ⟩
    (ι a + i * ι b) + (ι c + i * ι d)    ∎
    where open Eq.≡-Reasoning

  -- i i + 1 = 0.
  i²+1 : i * i + 1# ≡ 0#
  i²+1 = Eq.trans (Eq.cong (_+ 1#) i²) (AR.-‿inverseˡ 1#)

  ιᵍ-* : (x y : ℤi) → ιᵍ (x *ᵍ y) ≡ ιᵍ x * ιᵍ y
  ιᵍ-* (a +i b) (c +i d) = begin
    ι (a ℤ.* c ℤ.- b ℤ.* d) + i * ι (a ℤ.* d ℤ.+ b ℤ.* c)
      ≡⟨ Eq.cong₂ (λ u v → u + i * v)
           (Eq.trans (ι-- (a ℤ.* c) (b ℤ.* d)) (Eq.cong₂ (λ u v → u + - v) (ZS.*-homoℤ a c) (ZS.*-homoℤ b d)))
           (Eq.trans (ZS.+-homoℤ (a ℤ.* d) (b ℤ.* c)) (Eq.cong₂ _+_ (ZS.*-homoℤ a d) (ZS.*-homoℤ b c))) ⟩
    (A' * C' + - (B' * D')) + i * (A' * D' + B' * C')
      ≡⟨ solve 5 (λ a b c d i → (a :* c :+ :- (b :* d)) :+ i :* (a :* d :+ b :* c)
                               := (a :+ i :* b) :* (c :+ i :* d) :+ :- ((i :* i :+ con (+ 1)) :* (b :* d)))
           Eq.refl A' B' C' D' i ⟩
    (A' + i * B') * (C' + i * D') + - ((i * i + 1#) * (B' * D'))
      ≡⟨ Eq.cong (λ u → (A' + i * B') * (C' + i * D') + - (u * (B' * D'))) i²+1 ⟩
    (A' + i * B') * (C' + i * D') + - (0# * (B' * D'))
      ≡⟨ solve 5 (λ a b c d i → (a :+ i :* b) :* (c :+ i :* d) :+ :- (con (+ 0) :* (b :* d))
                               := (a :+ i :* b) :* (c :+ i :* d))
           Eq.refl A' B' C' D' i ⟩
    (A' + i * B') * (C' + i * D')       ∎
    where
    open Eq.≡-Reasoning
    A' = ι a
    B' = ι b
    C' = ι c
    D' = ι d

  ιᵍ-0 : ιᵍ 0ᵍ ≡ 0#
  ιᵍ-0 = Eq.trans (Eq.cong (λ u → 0# + u) (AR.zeroʳ i)) (AR.+-identityˡ 0#)

  ιᵍ-1 : ιᵍ 1ᵍ ≡ 1#
  ιᵍ-1 = Eq.trans (Eq.cong (λ u → 1# + u) (AR.zeroʳ i)) (AR.+-identityʳ 1#)

  ιᵍ-i : ιᵍ iᵍ ≡ i
  ιᵍ-i = Eq.trans (Eq.cong (λ u → 0# + u) (AR.*-identityʳ i)) (AR.+-identityˡ i)

  ιᵍ-dbl : (x : ℤi) → ιᵍ (dblᵍ x) ≡ ι (+ 2) * ιᵍ x
  ιᵍ-dbl (a +i b) = begin
    ι (+ 2 ℤ.* a) + i * ι (+ 2 ℤ.* b)   ≡⟨ Eq.cong₂ (λ u v → u + i * v) (ZS.*-homoℤ (+ 2) a) (ZS.*-homoℤ (+ 2) b) ⟩
    T * ι a + i * (T * ι b)             ≡⟨ solve 4 (λ t a b i → t :* a :+ i :* (t :* b) := t :* (a :+ i :* b))
                                             Eq.refl T (ι a) (ι b) i ⟩
    T * (ι a + i * ι b)                 ∎
    where
    open Eq.≡-Reasoning
    T = ι (+ 2)
