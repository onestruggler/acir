------------------------------------------------------------------------
-- Presentations of groups
--
-- The carry out of addition as a pseudo-Boolean polynomial
--
-- PathSum.Adder.Expansion counts the terms of the carry out of n-bit
-- addition as a Boolean polynomial, modulo 2: 2^n − 1.  A path-sum's
-- output enters its phase through its lift to D[x] (section 2, lemma
-- 2.5), and the lift that takes the values 0 and 1 exactly -- the
-- integer, or pseudo-Boolean, multilinear representation, which is
-- what PathSum.Polynomial.Boolean's liftᵉ builds and so what the output
-- polynomials of PathSum.Adder.Spec's specifications are -- is unique
-- (Polynomial.Boolean.lift-unique).  This module computes it for the
-- carry out, and counts its terms: (3^n − 1)/2.
--
-- The recursion.  With carry-in c, the carry out is that with carry-in
-- 0 plus c times the propagation Π_j (x_j ⊕ y_j), as integers too: the
-- two are never both 1 (carry-disjoint), so their exclusive or is their
-- sum.  So the lift satisfies C_(n+1) = C_n + x₀ y₀ D_n, with D_n the
-- lift of the propagation, Π_j (x_j + y_j − 2 x_j y_j), whose 3^n terms
-- are ±2^k (dZ); C_n has (3^n − 1)/2 (cZ).  Exactly as in the parity
-- case, by Möbius inversion at the head variables, now over the
-- integers (halvesᶻ, Quartersᶻ): every f whose values are the carry
-- out, as 0 or 1, has the coefficients cZ (carry-exact), and
-- 2 · #{non-zero coefficients} + 1 = 3^n (count-cZ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.Expansion.Lift where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ)
open import Data.Fin.Properties using (toℕ-fromℕ)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; divides; 0∣⇒≡0)
open import Data.Integer.Properties using
  (+-identityˡ; +-inverseʳ; *-identityʳ; *-identityˡ; *-zeroʳ;
   i*j≡0⇒i≡0∨j≡0)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (ℕ; zero; suc)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _^_ to _ℕ^_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import Data.Integer.Properties as ℤ
import Data.Nat.Solver as ℕSolver

open import PathSum.Adder.Binary using (maj; carry-out)
open import PathSum.Adder.Expansion using
  (dbl; ix; iy; xs; ys; prop; carry-out-in; empty; count-empty; nonzero)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Mobius using (evalˢ; values⇒coefficientsˢ)
open import PathSum.Polynomial.Count using (count; count-cong; count-false)
open import PathSum.Polynomial.Properties using (Σsub-0)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- Möbius inversion at the head variables, over the integers

private
  eval-head : (f : Subset (suc k) → ℤ) (b : Bool) (w : Fin k → Bool) →
              evalˢ f (b ∷ᵃ w) ≡
              (if b then evalˢ (λ s → f (inside ∷ s)) w else 0ℤ) +
              evalˢ (λ s → f (outside ∷ s)) w
  eval-head {k} f true  w = refl
  eval-head {k} f false w =
    cong (_+ evalˢ (λ s → f (outside ∷ s)) w) (Σsub-0 {k})

  undo : ∀ a b → a ≡ (a + b) - b
  undo = solve 2 (λ a b → a := (a :+ b) :- b) refl

-- The part without the head variable takes the values at head 0, the
-- quotient by it the differences of the values at head 1 and 0.

halvesᶻ : (f : Subset (suc k) → ℤ) (F : (Fin (suc k) → Bool) → ℤ) →
          (∀ v → evalˢ f v ≡ F v) →
          (∀ w → evalˢ (λ s → f (outside ∷ s)) w ≡ F (false ∷ᵃ w)) ×
          (∀ w → evalˢ (λ s → f (inside ∷ s)) w ≡
                 F (true ∷ᵃ w) - F (false ∷ᵃ w))
halvesᶻ f F h = low , high
  where
  low : ∀ w → evalˢ (λ s → f (outside ∷ s)) w ≡ F (false ∷ᵃ w)
  low w = trans (sym (+-identityˡ _))
                (trans (sym (eval-head f false w)) (h (false ∷ᵃ w)))

  high : ∀ w → evalˢ (λ s → f (inside ∷ s)) w ≡
               F (true ∷ᵃ w) - F (false ∷ᵃ w)
  high w = trans (undo (evalˢ (λ s → f (inside ∷ s)) w)
                       (evalˢ (λ s → f (outside ∷ s)) w))
                 (cong₂ _-_ (trans (sym (eval-head f true w)) (h (true ∷ᵃ w)))
                            (low w))

module Quartersᶻ {k : ℕ} (f : Subset (suc (suc k)) → ℤ)
                 (F : (Fin (suc (suc k)) → Bool) → ℤ)
                 (h : ∀ v → evalˢ f v ≡ F v) where

  q₀₀ : ∀ w → evalˢ (λ s → f (outside ∷ outside ∷ s)) w ≡
              F (false ∷ᵃ false ∷ᵃ w)
  q₀₀ = proj₁ (halvesᶻ (λ s → f (outside ∷ s)) (λ w → F (false ∷ᵃ w))
                       (proj₁ (halvesᶻ f F h)))

  q₁₀ : ∀ w → evalˢ (λ s → f (inside ∷ outside ∷ s)) w ≡
              F (true ∷ᵃ false ∷ᵃ w) - F (false ∷ᵃ false ∷ᵃ w)
  q₁₀ = proj₁ (halvesᶻ (λ s → f (inside ∷ s))
                       (λ w → F (true ∷ᵃ w) - F (false ∷ᵃ w))
                       (proj₂ (halvesᶻ f F h)))

  q₀₁ : ∀ w → evalˢ (λ s → f (outside ∷ inside ∷ s)) w ≡
              F (false ∷ᵃ true ∷ᵃ w) - F (false ∷ᵃ false ∷ᵃ w)
  q₀₁ = proj₂ (halvesᶻ (λ s → f (outside ∷ s)) (λ w → F (false ∷ᵃ w))
                       (proj₁ (halvesᶻ f F h)))

  q₁₁ : ∀ w → evalˢ (λ s → f (inside ∷ inside ∷ s)) w ≡
              (F (true ∷ᵃ true ∷ᵃ w) - F (false ∷ᵃ true ∷ᵃ w)) -
              (F (true ∷ᵃ false ∷ᵃ w) - F (false ∷ᵃ false ∷ᵃ w))
  q₁₁ = proj₂ (halvesᶻ (λ s → f (inside ∷ s))
                       (λ w → F (true ∷ᵃ w) - F (false ∷ᵃ w))
                       (proj₂ (halvesᶻ f F h)))


------------------------------------------------------------------------
-- The lifts

-- Π_{j<i} (x_j + y_j − 2 x_j y_j): one of x_j, y_j or x_j y_j for each
-- j < i, with a factor −2 for each x_j y_j.

dZ : Fin (suc n) → Subset (dbl n) → ℤ
dZ         zero     s                       = [ empty s ]ᶻ
dZ {zero}  (suc ())
dZ {suc n} (suc i)  (inside  ∷ outside ∷ s) = dZ i s
dZ {suc n} (suc i)  (outside ∷ inside  ∷ s) = dZ i s
dZ {suc n} (suc i)  (inside  ∷ inside  ∷ s) = - (+ 2) * dZ i s
dZ {suc n} (suc i)  (outside ∷ outside ∷ s) = 0ℤ

-- The carry out: C_(n+1) = C_n + x₀ y₀ D_n.

cZ : Subset (dbl n) → ℤ
cZ {zero}  []                      = 0ℤ
cZ {suc n} (outside ∷ outside ∷ s) = cZ s
cZ {suc n} (inside  ∷ inside  ∷ s) = dZ (fromℕ n) s
cZ {suc n} (inside  ∷ outside ∷ s) = 0ℤ
cZ {suc n} (outside ∷ inside  ∷ s) = 0ℤ


------------------------------------------------------------------------
-- Values determine coefficients

zero-exact : (f : Subset k → ℤ) → (∀ v → evalˢ f v ≡ 0ℤ) → ∀ s → f s ≡ 0ℤ
zero-exact f h s = 0∣⇒≡0 (values⇒coefficientsˢ 0ℤ f
  (λ v → subst (0ℤ ∣_) (sym (h v)) (divides 0ℤ refl)) s)

const-exact : (c : ℤ) (f : Subset k → ℤ) → (∀ v → evalˢ f v ≡ c) →
              ∀ s → f s ≡ c * [ empty s ]ᶻ
const-exact {zero}  c f h []            = trans (h (λ ())) (sym (*-identityʳ c))
const-exact {suc k} c f h (outside ∷ s) =
  const-exact c (λ s → f (outside ∷ s)) (proj₁ (halvesᶻ f (λ _ → c) h)) s
const-exact {suc k} c f h (inside  ∷ s) = trans
  (zero-exact (λ s → f (inside ∷ s))
              (λ w → trans (proj₂ (halvesᶻ f (λ _ → c) h) w) (+-inverseʳ c)) s)
  (sym (*-zeroʳ c))

private
  minus-0 : ∀ x c → x - c * 0ℤ ≡ x
  minus-0 = solve 2 (λ x c → x :- c :* con 0ℤ := x) refl

  both : ∀ c p → (c * 0ℤ - c * p) - (c * p - c * 0ℤ) ≡ (- (+ 2) * c) * p
  both = solve 2 (λ c p → (c :* con 0ℤ :- c :* p) :- (c :* p :- c :* con 0ℤ)
                          := (con (- (+ 2)) :* c) :* p) refl

  move : ∀ c d → (- (+ 2) * c) * d ≡ c * (- (+ 2) * d)
  move = solve 2 (λ c d → (con (- (+ 2)) :* c) :* d
                          := c :* (con (- (+ 2)) :* d)) refl

-- Scaled values c [Π_{j<i} p_j] have the coefficients c dZ i.

prop-exact : (c : ℤ) (i : Fin (suc n)) (f : Subset (dbl n) → ℤ) →
             (∀ v → evalˢ f v ≡ c * [ prop (xs v) (ys v) i ]ᶻ) →
             ∀ s → f s ≡ c * dZ i s
prop-exact         c zero    f h s =
  const-exact c f (λ v → trans (h v) (*-identityʳ c)) s
prop-exact {zero}  c (suc ())
prop-exact {suc n} c (suc i) f h (outside ∷ outside ∷ s) = trans
  (zero-exact _ (λ w → trans (Quartersᶻ.q₀₀ f F h w) (*-zeroʳ c)) s)
  (sym (*-zeroʳ c))
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = c * [ prop (xs v) (ys v) (suc i) ]ᶻ
prop-exact {suc n} c (suc i) f h (inside  ∷ outside ∷ s) =
  prop-exact c i _
    (λ w → trans (Quartersᶻ.q₁₀ f F h w)
                 (minus-0 (c * [ prop (xs w) (ys w) i ]ᶻ) c)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = c * [ prop (xs v) (ys v) (suc i) ]ᶻ
prop-exact {suc n} c (suc i) f h (outside ∷ inside  ∷ s) =
  prop-exact c i _
    (λ w → trans (Quartersᶻ.q₀₁ f F h w)
                 (minus-0 (c * [ prop (xs w) (ys w) i ]ᶻ) c)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = c * [ prop (xs v) (ys v) (suc i) ]ᶻ
prop-exact {suc n} c (suc i) f h (inside  ∷ inside  ∷ s) = trans
  (prop-exact (- (+ 2) * c) i _
    (λ w → trans (Quartersᶻ.q₁₁ f F h w)
                 (both c [ prop (xs w) (ys w) i ]ᶻ)) s)
  (move c (dZ i s))
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = c * [ prop (xs v) (ys v) (suc i) ]ᶻ

-- The carry out with carry-in 0 and the propagation are never both 1.

carry-disjoint : (a b : Fin n → Bool) →
                 carry-out a b false ∧ prop a b (fromℕ n) ≡ false
carry-disjoint {zero}  a b = refl
carry-disjoint {suc n} a b with a zero | b zero
... | true  | true  = ∧-zeroʳ _
... | true  | false = carry-disjoint (λ j → a (suc j)) (λ j → b (suc j))
... | false | true  = carry-disjoint (λ j → a (suc j)) (λ j → b (suc j))
... | false | false = ∧-zeroʳ _

private
  xor-disjoint : ∀ x p → x ∧ p ≡ false → [ x xor p ]ᶻ - [ x ]ᶻ ≡ [ p ]ᶻ
  xor-disjoint true  true  ()
  xor-disjoint true  false _ = refl
  xor-disjoint false true  _ = refl
  xor-disjoint false false _ = refl

  diff-cancel : ∀ x y → (x - y) - (y - y) ≡ x - y
  diff-cancel = solve 2 (λ x y → (x :- y) :- (y :- y) := x :- y) refl

-- So, as integers, the carry out with carry-in 1 less that with
-- carry-in 0 is the propagation.

carry-step : (a b : Fin n → Bool) →
             [ carry-out a b true ]ᶻ - [ carry-out a b false ]ᶻ ≡
             [ prop a b (fromℕ n) ]ᶻ
carry-step {n} a b = trans
  (cong (λ t → [ t ]ᶻ - [ carry-out a b false ]ᶻ) (carry-out-in a b true))
  (xor-disjoint (carry-out a b false) (prop a b (fromℕ n))
                (carry-disjoint a b))

-- Every f whose values are the carry out, as 0 or 1, is cZ.

carry-exact : (f : Subset (dbl n) → ℤ) →
              (∀ v → evalˢ f v ≡ [ carry-out (xs v) (ys v) false ]ᶻ) →
              ∀ s → f s ≡ cZ s
carry-exact {zero}  f h []                      = h (λ ())
carry-exact {suc n} f h (outside ∷ outside ∷ s) =
  carry-exact _ (Quartersᶻ.q₀₀ f F h) s
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = [ carry-out (xs v) (ys v) false ]ᶻ
carry-exact {suc n} f h (inside  ∷ outside ∷ s) =
  zero-exact _ (λ w → trans (Quartersᶻ.q₁₀ f F h w)
                            (+-inverseʳ [ carry-out (xs w) (ys w) false ]ᶻ)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = [ carry-out (xs v) (ys v) false ]ᶻ
carry-exact {suc n} f h (outside ∷ inside  ∷ s) =
  zero-exact _ (λ w → trans (Quartersᶻ.q₀₁ f F h w)
                            (+-inverseʳ [ carry-out (xs w) (ys w) false ]ᶻ)) s
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = [ carry-out (xs v) (ys v) false ]ᶻ
carry-exact {suc n} f h (inside  ∷ inside  ∷ s) = trans
  (prop-exact 1ℤ (fromℕ n) _
    (λ w → trans (Quartersᶻ.q₁₁ f F h w)
           (trans (diff-cancel [ carry-out (xs w) (ys w) true ]ᶻ
                               [ carry-out (xs w) (ys w) false ]ᶻ)
           (trans (carry-step (xs w) (ys w))
                  (sym (*-identityˡ [ prop (xs w) (ys w) (fromℕ n) ]ᶻ))))) s)
  (*-identityˡ (dZ (fromℕ n) s))
  where
  F : (Fin (dbl (suc n)) → Bool) → ℤ
  F v = [ carry-out (xs v) (ys v) false ]ᶻ


------------------------------------------------------------------------
-- Counting the terms

private
  nonzero-bit : ∀ b → nonzero [ b ]ᶻ ≡ b
  nonzero-bit true  = refl
  nonzero-bit false = refl

  nonzero-0 : nonzero 0ℤ ≡ false
  nonzero-0 = refl

  nonzero-−2 : ∀ z → nonzero (- (+ 2) * z) ≡ nonzero z
  nonzero-−2 z with z ℤ.≟ 0ℤ | (- (+ 2) * z) ℤ.≟ 0ℤ
  ... | yes refl | yes _  = refl
  ... | yes refl | no ¬e  = contradiction refl ¬e
  ... | no z≢0   | yes e  =
        contradiction e (λ e′ → [ (λ ()) , z≢0 ]′ (i*j≡0⇒i≡0∨j≡0 (- (+ 2)) e′))
  ... | no _     | no _   = refl

  triple : ∀ a → (a ℕ+ a) ℕ+ (a ℕ+ 0) ≡ 3 ℕ* a
  triple = ℕSolver.+-*-Solver.solve 1 (λ a →
    (a ℕSolver.+-*-Solver.:+ a) ℕSolver.+-*-Solver.:+
    (a ℕSolver.+-*-Solver.:+ ℕSolver.+-*-Solver.con 0)
    ℕSolver.+-*-Solver.:= ℕSolver.+-*-Solver.con 3 ℕSolver.+-*-Solver.:* a)
    refl

  carry-count-step : ∀ t c → suc (2 ℕ* ((t ℕ+ 0) ℕ+ (0 ℕ+ c))) ≡
                             (2 ℕ* t) ℕ+ suc (2 ℕ* c)
  carry-count-step = ℕSolver.+-*-Solver.solve 2 (λ t c →
    ℕSolver.+-*-Solver.con 1 ℕSolver.+-*-Solver.:+
      ℕSolver.+-*-Solver.con 2 ℕSolver.+-*-Solver.:*
      ((t ℕSolver.+-*-Solver.:+ ℕSolver.+-*-Solver.con 0)
       ℕSolver.+-*-Solver.:+ (ℕSolver.+-*-Solver.con 0 ℕSolver.+-*-Solver.:+ c))
    ℕSolver.+-*-Solver.:=
    (ℕSolver.+-*-Solver.con 2 ℕSolver.+-*-Solver.:* t) ℕSolver.+-*-Solver.:+
      (ℕSolver.+-*-Solver.con 1 ℕSolver.+-*-Solver.:+
       ℕSolver.+-*-Solver.con 2 ℕSolver.+-*-Solver.:* c)) refl

  two-plus-one : ∀ t → (2 ℕ* t) ℕ+ t ≡ 3 ℕ* t
  two-plus-one = ℕSolver.+-*-Solver.solve 1 (λ t →
    (ℕSolver.+-*-Solver.con 2 ℕSolver.+-*-Solver.:* t) ℕSolver.+-*-Solver.:+ t
    ℕSolver.+-*-Solver.:= ℕSolver.+-*-Solver.con 3 ℕSolver.+-*-Solver.:* t)
    refl

-- 3^i terms in the propagation ...

count-dZ : (i : Fin (suc n)) → count (λ s → nonzero (dZ i s)) ≡ 3 ℕ^ toℕ i
count-dZ {n}     zero    =
  trans (count-cong {dbl n} (λ s → nonzero-bit (empty s))) (count-empty {dbl n})
count-dZ {suc n} (suc i) =
  trans (cong₂ _ℕ+_
          (cong₂ _ℕ+_ (trans (count-cong {dbl n} (λ s → nonzero-−2 (dZ i s)))
                             (count-dZ i))
                      (count-dZ i))
          (cong₂ _ℕ+_ (count-dZ i) (count-false {dbl n})))
        (triple (3 ℕ^ toℕ i))

-- ... and (3^n − 1)/2 in the carry out.

count-cZ : suc (2 ℕ* count (λ s → nonzero (cZ {n} s))) ≡ 3 ℕ^ n
count-cZ {zero}  = refl
count-cZ {suc n} = begin
  suc (2 ℕ* ((count (λ s → nonzero (dZ (fromℕ n) s)) ℕ+
              count {dbl n} (λ _ → false)) ℕ+
             (count {dbl n} (λ _ → false) ℕ+
              count (λ s → nonzero (cZ {n} s)))))
    ≡⟨ cong (λ t → suc (2 ℕ* t))
            (cong₂ _ℕ+_ (cong₂ _ℕ+_ (count-dZ (fromℕ n)) (count-false {dbl n}))
                        (cong (_ℕ+ count (λ s → nonzero (cZ {n} s)))
                              (count-false {dbl n}))) ⟩
  suc (2 ℕ* ((3 ℕ^ toℕ (fromℕ n) ℕ+ 0) ℕ+
             (0 ℕ+ count (λ s → nonzero (cZ {n} s)))))
    ≡⟨ cong (λ t → suc (2 ℕ* ((3 ℕ^ t ℕ+ 0) ℕ+
                              (0 ℕ+ count (λ s → nonzero (cZ {n} s))))))
            (toℕ-fromℕ n) ⟩
  suc (2 ℕ* ((3 ℕ^ n ℕ+ 0) ℕ+ (0 ℕ+ count (λ s → nonzero (cZ {n} s)))))
    ≡⟨ carry-count-step (3 ℕ^ n) (count (λ s → nonzero (cZ {n} s))) ⟩
  (2 ℕ* 3 ℕ^ n) ℕ+ suc (2 ℕ* count (λ s → nonzero (cZ {n} s)))
    ≡⟨ cong ((2 ℕ* 3 ℕ^ n) ℕ+_) (count-cZ {n}) ⟩
  (2 ℕ* 3 ℕ^ n) ℕ+ 3 ℕ^ n
    ≡⟨ two-plus-one (3 ℕ^ n) ⟩
  3 ℕ* 3 ℕ^ n
    ∎
  where open ≡-Reasoning
