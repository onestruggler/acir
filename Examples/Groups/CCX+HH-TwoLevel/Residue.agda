------------------------------------------------------------------------
-- Presentations of groups
--
-- Residues modulo 4.  An odd integer is ≡ 1 or ≡ 3 (mod 4); τ w says
-- which (τ w = true for 3), and sgn (τ w) w, the integer negated if
-- τ w, is ≡ 1 (mod 4): it is 1 + 4z for some z (one4).  These are the
-- exponents of the (-1)'s of Algorithm 1 (step 14, Lemma 3.1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Residue where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
import Data.Integer.Solver as ℤSolver
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℕ ; oddℤ ; oddℤ-neg ; oddℤ-+ ; oddℤ-*)

private
  module ℤS = ℤSolver.+-*-Solver
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- The residue 3

-- Is a natural number ≡ 3 (mod 4)?
τℕ : ℕ → Bool
τℕ 0 = false
τℕ 1 = false
τℕ 2 = false
τℕ 3 = true
τℕ (suc (suc (suc (suc m)))) = τℕ m

-- Is an integer ≡ 3 (mod 4)?  (-(m + 1) ≡ 3 iff m + 3 ≡ 3.)
τ : ℤ → Bool
τ (+ m)     = τℕ m
τ -[1+ m ]  = τℕ (suc (suc (suc m)))

-- Negation if the flag is set.
sgn : Bool → ℤ → ℤ
sgn true  w = ℤ.- w
sgn false w = w

sgn-not-neg : ∀ t w → sgn (not t) (ℤ.- w) ≡ sgn t w
sgn-not-neg true  w = refl
sgn-not-neg false w = ℤP.neg-involutive w

private
  odd4 : ∀ m → oddℕ (suc (suc (suc (suc m)))) ≡ oddℕ m
  odd4 m = trans (BoolP.not-involutive (not (not (oddℕ m)))) (BoolP.not-involutive (oddℕ m))

  -- Odd numbers alternate between the residues 1 and 3.
  τℕ-flip : ∀ k → oddℕ k ≡ true → τℕ (suc (suc k)) ≡ not (τℕ k)
  τℕ-flip 1 _ = refl
  τℕ-flip 3 _ = refl
  τℕ-flip (suc (suc (suc (suc k)))) o = τℕ-flip k (trans (sym (odd4 k)) o)
  τℕ-flip 0 ()
  τℕ-flip 2 ()

  one4ℕ : ∀ m → oddℕ m ≡ true → ∃ λ z → sgn (τℕ m) (+ m) ≡ + 1 ℤ.+ + 4 ℤ.* z
  one4ℕ 1 _ = + 0 , refl
  one4ℕ 3 _ = -[1+ 0 ] , refl
  one4ℕ (suc (suc (suc (suc m)))) o with τℕ m | one4ℕ m (trans (sym (odd4 m)) o)
  ... | false | z , e = z ℤ.+ + 1 , (begin
    + 4 ℤ.+ + m                        ≡⟨ cong (λ t → + 4 ℤ.+ t) e ⟩
    + 4 ℤ.+ (+ 1 ℤ.+ + 4 ℤ.* z)        ≡⟨ ℤS.solve 1 (λ z → con (+ 4) :+ (con (+ 1) :+ con (+ 4) :* z)
                                              := con (+ 1) :+ con (+ 4) :* (z :+ con (+ 1))) refl z ⟩
    + 1 ℤ.+ + 4 ℤ.* (z ℤ.+ + 1)        ∎)
    where open ≡-Reasoning
  ... | true | z , e = z ℤ.- + 1 , (begin
    ℤ.- (+ 4 ℤ.+ + m)                  ≡⟨ ℤP.neg-distrib-+ (+ 4) (+ m) ⟩
    ℤ.- (+ 4) ℤ.+ ℤ.- (+ m)            ≡⟨ cong (λ t → ℤ.- (+ 4) ℤ.+ t) e ⟩
    ℤ.- (+ 4) ℤ.+ (+ 1 ℤ.+ + 4 ℤ.* z)  ≡⟨ ℤS.solve 1 (λ z → :- con (+ 4) :+ (con (+ 1) :+ con (+ 4) :* z)
                                              := con (+ 1) :+ con (+ 4) :* (z :- con (+ 1))) refl z ⟩
    + 1 ℤ.+ + 4 ℤ.* (z ℤ.- + 1)        ∎)
    where open ≡-Reasoning
  one4ℕ 0 ()
  one4ℕ 2 ()

-- An odd integer, negated if ≡ 3 (mod 4), is 1 + 4z.
one4 : ∀ w → oddℤ w ≡ true → ∃ λ z → sgn (τ w) w ≡ + 1 ℤ.+ + 4 ℤ.* z
one4 (+ m) o = one4ℕ m o
one4 -[1+ m ] o with one4ℕ (suc m) o
... | z , e = z , trans (cong (λ t → sgn t (ℤ.- (+ suc m))) (τℕ-flip (suc m) o)) (trans (sgn-not-neg (τℕ (suc m)) (+ suc m)) e)

------------------------------------------------------------------------
-- The residue is determined

private
  τℕ-4 : ∀ r q → τℕ (r ℕ.+ 4 ℕ.* q) ≡ τℕ r
  τℕ-4 r zero = cong τℕ (ℕP.+-identityʳ r)
  τℕ-4 r (suc q) = trans (cong τℕ (shift r q)) (τℕ-4 r q)
    where
    shift : ∀ r q → r ℕ.+ 4 ℕ.* suc q ≡ suc (suc (suc (suc (r ℕ.+ 4 ℕ.* q))))
    shift r q = trans (cong (r ℕ.+_) (ℕP.*-suc 4 q))
                      (trans (sym (ℕP.+-assoc r 4 (4 ℕ.* q)))
                             (cong (ℕ._+ 4 ℕ.* q) (ℕP.+-comm r 4)))

-- 1 + 4z is ≡ 1.
τ-one : ∀ z → τ (+ 1 ℤ.+ + 4 ℤ.* z) ≡ false
τ-one (+ q) = trans (cong (λ t → τ (+ 1 ℤ.+ t)) (sym (ℤP.pos-* 4 q))) (τℕ-4 1 q)
τ-one -[1+ q ] = trans (cong τ eq) (τℕ-4 5 q)
  where
  -- 1 - 4(q + 1) = -(4q + 3) = -[1+ (4q + 2)].
  eq : + 1 ℤ.+ + 4 ℤ.* -[1+ q ] ≡ -[1+ (2 ℕ.+ 4 ℕ.* q) ]
  eq = begin
    + 1 ℤ.+ + 4 ℤ.* -[1+ q ]                ≡⟨ ℤS.solve 1 (λ q → con (+ 1) :+ con (+ 4) :* (:- (con (+ 1) :+ q))
                                                      := :- (con (+ 3) :+ con (+ 4) :* q)) refl (+ q) ⟩
    ℤ.- (+ 3 ℤ.+ + 4 ℤ.* + q)               ≡⟨ cong (λ t → ℤ.- (+ 3 ℤ.+ t)) (sym (ℤP.pos-* 4 q)) ⟩
    ℤ.- (+ (3 ℕ.+ 4 ℕ.* q))                 ≡⟨⟩
    -[1+ (2 ℕ.+ 4 ℕ.* q) ]                  ∎
    where open ≡-Reasoning

-- Negation flips the residue of an odd integer.
τ-neg : ∀ w → oddℤ w ≡ true → τ (ℤ.- w) ≡ not (τ w)
τ-neg (+ zero) ()
τ-neg (+ suc m) o = τℕ-flip (suc m) o
τ-neg -[1+ m ] o = sym (trans (cong not (τℕ-flip (suc m) o)) (BoolP.not-involutive (τℕ (suc m))))

-- The flag that makes an odd integer ≡ 1 is τ.
τ-char : ∀ t w z → oddℤ w ≡ true → sgn t w ≡ + 1 ℤ.+ + 4 ℤ.* z → τ w ≡ t
τ-char false w z o e = trans (cong τ e) (τ-one z)
τ-char true w z o e = begin
  τ w                    ≡⟨ sym (BoolP.not-involutive (τ w)) ⟩
  not (not (τ w))        ≡⟨ cong not (sym (τ-neg w o)) ⟩
  not (τ (ℤ.- w))        ≡⟨ cong (λ x → not (τ x)) e ⟩
  not (τ (+ 1 ℤ.+ + 4 ℤ.* z)) ≡⟨ cong not (τ-one z) ⟩
  true                   ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Odd integers as 1 + 2y

-- An odd integer is 1 + 2y, with y odd iff it is ≡ 3 (mod 4).
one2 : ∀ w → oddℤ w ≡ true → ∃ λ y → w ≡ + 1 ℤ.+ + 2 ℤ.* y × oddℤ y ≡ τ w
one2 w o with τ w in eτ | one4 w o
... | false | z , e = + 2 ℤ.* z , trans e (ℤS.solve 1 (λ z → con (+ 1) :+ con (+ 4) :* z := con (+ 1) :+ con (+ 2) :* (con (+ 2) :* z)) refl z)
                                , oddℤ-* (+ 2) z
... | true | z , e = ℤ.- (+ 1) ℤ.- + 2 ℤ.* z , (begin
  w                                      ≡⟨ sym (ℤP.neg-involutive w) ⟩
  ℤ.- (ℤ.- w)                            ≡⟨ cong ℤ.-_ e ⟩
  ℤ.- (+ 1 ℤ.+ + 4 ℤ.* z)                ≡⟨ ℤS.solve 1 (λ z → :- (con (+ 1) :+ con (+ 4) :* z)
                                                := con (+ 1) :+ con (+ 2) :* (:- con (+ 1) :- con (+ 2) :* z)) refl z ⟩
  + 1 ℤ.+ + 2 ℤ.* (ℤ.- (+ 1) ℤ.- + 2 ℤ.* z) ∎) , oddness
  where
  open ≡-Reasoning
  oddness : oddℤ (ℤ.- (+ 1) ℤ.- + 2 ℤ.* z) ≡ true
  oddness = trans (oddℤ-+ (ℤ.- (+ 1)) (ℤ.- (+ 2 ℤ.* z)))
                  (cong (true xor_) (trans (oddℤ-neg (+ 2 ℤ.* z)) (oddℤ-* (+ 2) z)))

------------------------------------------------------------------------
-- Pairs of odd integers

-- Two odd integers with sum 2m have equal residues iff m is odd.
τ-pair : ∀ p q m → oddℤ p ≡ true → oddℤ q ≡ true → p ℤ.+ q ≡ + 2 ℤ.* m →
         τ p xor τ q ≡ not (oddℤ m)
τ-pair p q m op oq e with one2 p op | one2 q oq
... | yp , ep , τp | yq , eq , τq = begin
  τ p xor τ q                              ≡⟨ cong₂ _xor_ (sym τp) (sym τq) ⟩
  oddℤ yp xor oddℤ yq                      ≡⟨ sym (BoolP.not-involutive _) ⟩
  not (not (oddℤ yp xor oddℤ yq))          ≡⟨ cong not (sym (trans (oddℤ-+ (+ 1) (yp ℤ.+ yq)) (cong (true xor_) (oddℤ-+ yp yq)))) ⟩
  not (oddℤ (+ 1 ℤ.+ (yp ℤ.+ yq)))         ≡⟨ cong (λ x → not (oddℤ x)) m≡ ⟩
  not (oddℤ m)                             ∎
  where
  open ≡-Reasoning
  m≡ : + 1 ℤ.+ (yp ℤ.+ yq) ≡ m
  m≡ = ℤP.*-cancelˡ-≡ (+ 2) _ _ (trans
    (ℤS.solve 2 (λ yp yq → con (+ 2) :* (con (+ 1) :+ (yp :+ yq))
                   := (con (+ 1) :+ con (+ 2) :* yp) :+ (con (+ 1) :+ con (+ 2) :* yq)) refl yp yq)
    (trans (cong₂ ℤ._+_ (sym ep) (sym eq)) e))
