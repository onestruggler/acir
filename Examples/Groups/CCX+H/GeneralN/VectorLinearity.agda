------------------------------------------------------------------------
-- Presentations of groups
--
-- An action given by finite matrix rows preserves linear combinations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+H.GeneralN.VectorLinearity
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj) where

open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (Matrix)
open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCR adjI
  using (_!_ ; vec-ext ; sum ; ent ; ∑-distrib-+ ; sum-cong-≗ ; *-distribˡ-sum)
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as Algebra
import Algebra.Properties.Ring as RP

private
  module R = IsCommutativeRing isCR
  module M = Algebra isCR adjI
  module Laws = RP M.AR.ring
  variable n : ℕ

combine : A → A → Vec A n → Vec A n → Vec A n
combine a b = zipWith (λ x y → a * x + b * y)

combine-! : ∀ a b (u v : Vec A n) i →
  combine a b u v ! i ≡ a * (u ! i) + b * (v ! i)
combine-! a b u v i = VP.lookup-zipWith (λ x y → a * x + b * y) i u v

Linear : (Vec A n → Vec A n) → Set
Linear f = ∀ a b u v → f (combine a b u v) ≡ combine a b (f u) (f v)

compose : ∀ (f g : Vec A n → Vec A n) → Linear f → Linear g → Linear (λ v → f (g v))
compose f g lf lg a b u v = trans (cong f (lg a b u v)) (lf a b (g u) (g v))

plus minus : A → Vec A n → Vec A n → Vec A n
plus a = zipWith (λ x y → a * (x + y))
minus a = zipWith (λ x y → a * (x + - y))

private
  plus-combine : ∀ a (u v : Vec A n) → plus a u v ≡ combine a a u v
  plus-combine a [] [] = refl
  plus-combine a (x ∷ u) (y ∷ v) = cong₂ _∷_ (R.distribˡ a x y) (plus-combine a u v)

  minus-combine : ∀ a (u v : Vec A n) → minus a u v ≡ combine a (- a) u v
  minus-combine a [] [] = refl
  minus-combine a (x ∷ u) (y ∷ v) = cong₂ _∷_
    (trans (R.distribˡ a x (- y))
      (cong (a * x +_) (trans (sym (Laws.-‿distribʳ-* a y)) (Laws.-‿distribˡ-* a y))))
    (minus-combine a u v)

plus-linear : ∀ (f : Vec A n → Vec A n) → Linear f → ∀ a u v →
  f (plus a u v) ≡ plus a (f u) (f v)
plus-linear f linear a u v = trans (cong f (plus-combine a u v))
  (trans (linear a a u v) (sym (plus-combine a (f u) (f v))))

minus-linear : ∀ (f : Vec A n → Vec A n) → Linear f → ∀ a u v →
  f (minus a u v) ≡ minus a (f u) (f v)
minus-linear f linear a u v = trans (cong f (minus-combine a u v))
  (trans (linear a (- a) u v) (sym (minus-combine a (f u) (f v))))

private
  swap-scale : ∀ c a x → c * (a * x) ≡ a * (c * x)
  swap-scale c a x = trans (sym (R.*-assoc c a x))
    (trans (cong (_* x) (R.*-comm c a)) (R.*-assoc a c x))

  distribute : ∀ c a b x y → c * (a * x + b * y) ≡ a * (c * x) + b * (c * y)
  distribute c a b x y = trans (R.distribˡ c (a * x) (b * y))
    (cong₂ _+_ (swap-scale c a x) (swap-scale c b y))

by-matrix : ∀ (M : Matrix n n A) (f : Vec A n → Vec A n) →
  (∀ v r → f v ! r ≡ sum (λ i → ent M r i * (v ! i))) → Linear f
by-matrix M f row a b u v = vec-ext λ r →
  trans (row (combine a b u v) r)
    (trans (sum-cong-≗ (λ i → trans
      (cong (ent M r i *_) (combine-! a b u v i))
      (distribute (ent M r i) a b (u ! i) (v ! i))))
      (trans (∑-distrib-+ (λ i → a * (ent M r i * (u ! i)))
        (λ i → b * (ent M r i * (v ! i))))
        (trans (cong₂ _+_
          (sym (*-distribˡ-sum a (λ i → ent M r i * (u ! i))))
          (sym (*-distribˡ-sum b (λ i → ent M r i * (v ! i)))))
          (trans (cong₂ (λ x y → a * x + b * y) (sym (row u r)) (sym (row v r)))
            (sym (combine-! a b (f u) (f v) r))))))
