------------------------------------------------------------------------
-- Presentations of groups
--
-- A path-sum without path variables is the identity exactly when it has
-- no normalisation and the identity's polynomials
--
-- Corollary 4.4 ends when the restriction of a circuit "reduces to
-- |x⟩ ↦ |x⟩": a statement about the reduct's polynomials, not about
-- its operator.  PathSum.Identity's id-if is the easy direction --
-- outputs that are the inputs modulo 2 and a phase that vanishes
-- modulo 2^M, coefficient by coefficient, at no normalisation, make
-- the identity.  This module proves the converse, so the syntactic
-- test is exactly the semantic one.
--
-- The converse goes through the input-by-input characterisation of
-- PathSum.Decide.  An identity spends no normalisation, and at every
-- input x its single path returns x with a phase ≡ 0 modulo 2^M.  So
-- every output polynomial takes the value x_w modulo 2 at every
-- Boolean point x, and the phase the value 0 modulo 2^M.  Möbius
-- inversion (PathSum.Mobius) turns "divisible at every point" into
-- "divisible coefficient by coefficient", which is id-if's hypothesis.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Syntactic (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.DivMod using (_/_; _%_; n%d<d; a≡a%n+[a/n]*n)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides)
open import Data.Integer.Properties using (+-identityʳ; +-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (s≤s; z≤n) renaming (_<_ to _<ℕ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Decide M₀ using (id-no-norm; id-only-if′)
open import PathSum.Denotation M₀ using
  (Assign; outBit; hits-elim; _≋_; eval-μ-val)
open import PathSum.Identity M₀ using (id-if)
open import PathSum.Mobius using (values⇒coefficients)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; eval; μ; x[_]; 0ᴾ; _-ᴾ_; _≈[_]_)
open import PathSum.Polynomial.Properties using (eval-−ᴾ)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Reading an output modulo 2

-- An output reads as the bit b exactly when its value differs from b
-- by an even number.  Only the forward direction is needed: an integer
-- that is not even is one more than an even one.

private
  odd : ∀ e → ¬ ((+ 2) ∣ e) → (+ 2) ∣ (e - 1ℤ)
  odd e ¬even = go (e % (+ 2)) (n%d<d e (+ 2)) (a≡a%n+[a/n]*n e (+ 2))
    where
    shape : ∀ q → (1ℤ + q * (+ 2)) - 1ℤ ≡ q * (+ 2)
    shape = solve 1 (λ q → (con 1ℤ :+ q :* con (+ 2)) :- con 1ℤ
                           := q :* con (+ 2)) refl

    go : ∀ r → r <ℕ 2 → e ≡ (+ r) + (e / (+ 2)) * (+ 2) →
         (+ 2) ∣ (e - 1ℤ)
    go zero          _                 eq = contradiction
      (divides (e / (+ 2)) (trans eq (+-identityˡ _))) ¬even
    go (suc zero)    _                 eq =
      divides (e / (+ 2)) (trans (cong (_- 1ℤ) eq) (shape (e / (+ 2))))
    go (suc (suc r)) (s≤s (s≤s ())) _

  from-dec : ∀ {e : ℤ} (d : Dec ((+ 2) ∣ e)) (b : Bool) →
             not ⌊ d ⌋ ≡ b → (+ 2) ∣ (e - [ b ]ᶻ)
  from-dec {e} (yes even)  false _  =
    subst ((+ 2) ∣_) (sym (+-identityʳ e)) even
  from-dec {e} (no  ¬even) true  _  = odd e ¬even
  from-dec     (yes _)     true  ()
  from-dec     (no  _)     false ()

outBit-∣ : (ξ : PathSum n k m) (x : Assign n) (y : Assign m) (w : Fin n)
           (b : Bool) → outBit ξ x y w ≡ b →
           (+ 2) ∣ (eval (out ξ w) x y - [ b ]ᶻ)
outBit-∣ ξ x y w b = from-dec ((+ 2) ∣? eval (out ξ w) x y) b


------------------------------------------------------------------------
-- The converse of id-if

-- The identity's outputs are the inputs modulo 2, and its phase
-- vanishes modulo 2^M, coefficient by coefficient.

id-only-if : (ξ : PathSum n 0 0) → ξ ≋ idPS →
             (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) × phase ξ ≈[ pow M ] 0ᴾ
id-only-if ξ ξ≋id = outs , ph
  where
  per = id-only-if′ ξ ξ≋id

  -- At every point, output w takes the value x_w modulo 2.
  outs : ∀ w → out ξ w ≈[ + 2 ] μ x[ w ]
  outs w = values⇒coefficients (+ 2) (out ξ w -ᴾ μ x[ w ]) (λ x y →
    subst ((+ 2) ∣_)
      (sym (trans (eval-−ᴾ (out ξ w) (μ x[ w ]) x y)
                  (cong (λ v → eval (out ξ w) x y - v)
                        (eval-μ-val x[ w ] x y))))
      (outBit-∣ ξ x y w (x w) (hits-elim ξ x y x (proj₁ per x y) w)))

  -- And the phase takes a value ≡ 0 modulo 2^M at every point.
  ph : phase ξ ≈[ pow M ] 0ᴾ
  ph γ = subst (pow M ∣_) (sym (+-identityʳ (phase ξ γ)))
    (values⇒coefficients (pow M) (phase ξ) (proj₂ per) γ)

-- So a path-sum without path variables is the identity exactly when it
-- has the identity's polynomials and no normalisation.

id⇔syntactic : (ξ : PathSum n k 0) →
               (ξ ≋ idPS ⇔
                (k ≡ 0 ×
                 (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) ×
                 phase ξ ≈[ pow M ] 0ᴾ))
id⇔syntactic {k = zero}  ξ = mk⇔
  (λ ξ≋id → refl , id-only-if ξ ξ≋id)
  (λ (_ , outs , ph) → id-if ξ outs ph)
id⇔syntactic {k = suc k} ξ = mk⇔
  (λ ξ≋id → contradiction ξ≋id (id-no-norm ξ))
  (λ { (() , _) })
