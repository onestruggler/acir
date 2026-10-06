------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 2.1: the worked composition, and the lifting of x ⊕ y
--
-- Two instances section 2.1 of Amy's QPL 2018 paper works out in its
-- text, checked at the examples' precision M₀ = 0 (eighths: ¼ is 2
-- and ½ is 4).
--
-- * Composition.  "We can compute the composition of
--   |x1 x2 x3⟩ ↦ |x1 (x1 ⊕ x2) x3⟩ followed by
--   |x1′ x2′ x3′⟩ ↦ |x1′ x2′ (x2′ ⊕ x3′)⟩ by substituting x2′ with
--   x1 ⊕ x2: |x1 x2 x3⟩ ↦ |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3)⟩."  Here the
--   two path-sums are cnot₁₂ and cnot₂₃ and their composite is
--   cnot₂₃ ∘ᴾ cnot₁₂, definition 2.6 as PathSum.Compose implements it
--   (a simultaneous substitution of the lifts of cnot₁₂'s outputs).
--   Its polynomials are built by PathSum.Polynomial.Bind's bind, which
--   is opaque and never computed; they are read through their values
--   (PathSum.Compose.Properties.outBit-∘ and eval-∘), and Möbius
--   inversion (PathSum.Polynomial.Boolean.≈-from-values) turns the
--   values into coefficients.  So the composite is congruent to the
--   paper's result, cnot₁₃: every output coefficient by coefficient
--   modulo 2, and the phase, 0, coefficient by coefficient modulo 1
--   (composite-congruent); hence the two are equivalent
--   (composite-≋).
--
-- * Lifting.  "For all x, y ∈ Z₂, ¼(x ⊕ y) = ¼x + ¼y − ½xy."  The
--   identity holds of the values (lift-instance-values), and of the
--   polynomials: the lift of the Boolean polynomial x ⊕ y that
--   PathSum.Polynomial.Boolean.liftᴮ computes (the one definition 2.6
--   substitutes) is x + y − 2xy coefficient by coefficient, by the
--   recursion P ⊕ Q = P + Q − 2PQ (lift-xor), so ¼ times it is
--   ¼x + ¼y − ½xy coefficient by coefficient, as integers and not only
--   modulo 1 (lift-instance).  Both are checked by computation at the
--   four monomials in x and y.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Section21 where

open import Data.Bool.Base using (Bool; true; false; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties 0 using (eval-∘; outBit-∘)
open import PathSum.Compose.Sum 0 using (_++ᵃ_)
open import PathSum.Congruence 0 using (Congruent; congruent-≋)
open import PathSum.Denotation 0 using (Assign; outBit; _≋_)
open import PathSum.HiddenShift.Sign 0 using (odd-+; odd-[]; odd-≡)
open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using
  (Poly; Mon; μ; x[_]; 0ᴾ; _+ᴾ_; _-ᴾ_; _·ᴾ_; eval; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using (≈-from-values; liftᴮ)
open import PathSum.Polynomial.Product using (monoᴾ; eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ; eval-cong; i∣0)
open import PathSum.Reduction 3 using (¼; ½)


------------------------------------------------------------------------
-- The three path-sums

-- The input variables x1, x2, x3 as polynomials.

X₁ X₂ X₃ : Poly 3 0
X₁ = μ x[ zero ]
X₂ = μ x[ suc zero ]
X₃ = μ x[ suc (suc zero) ]

-- |x1 x2 x3⟩ ↦ |x1 (x1 ⊕ x2) x3⟩.

outs₁₂ : Fin 3 → Poly 3 0
outs₁₂ zero             = X₁
outs₁₂ (suc zero)       = X₁ +ᴾ X₂
outs₁₂ (suc (suc zero)) = X₃

cnot₁₂ : PathSum 3 0 0
cnot₁₂ = ⟨ 0ᴾ , outs₁₂ ⟩

-- |x1′ x2′ x3′⟩ ↦ |x1′ x2′ (x2′ ⊕ x3′)⟩.

outs₂₃ : Fin 3 → Poly 3 0
outs₂₃ zero             = X₁
outs₂₃ (suc zero)       = X₂
outs₂₃ (suc (suc zero)) = X₂ +ᴾ X₃

cnot₂₃ : PathSum 3 0 0
cnot₂₃ = ⟨ 0ᴾ , outs₂₃ ⟩

-- The paper's result, |x1 x2 x3⟩ ↦ |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3)⟩.

outs₁₃ : Fin 3 → Poly 3 0
outs₁₃ zero             = X₁
outs₁₃ (suc zero)       = X₁ +ᴾ X₂
outs₁₃ (suc (suc zero)) = X₁ +ᴾ X₂ +ᴾ X₃

cnot₁₃ : PathSum 3 0 0
cnot₁₃ = ⟨ 0ᴾ , outs₁₃ ⟩

-- First cnot₁₂, then cnot₂₃ (definition 2.6).

composite : PathSum 3 0 0
composite = cnot₂₃ ∘ᴾ cnot₁₂


------------------------------------------------------------------------
-- Reading parities

private
  none : Assign 0
  none ()

  -- The parity of a sum of input variables.

  odd-X : ∀ {n m} (i : Fin n) (x : Assign n) (y : Assign m) →
          odd (eval (μ x[ i ]) x y) ≡ x i
  odd-X i x y = trans (cong odd (eval-μᴾ x[ i ] x y)) (odd-[] (x i))

  odd-+X : ∀ {n m} (P : Poly n m) (i : Fin n) (x : Assign n) (y : Assign m) →
           odd (eval (P +ᴾ μ x[ i ]) x y) ≡ odd (eval P x y) xor x i
  odd-+X P i x y = trans (cong odd (eval-+ᴾ P (μ x[ i ]) x y))
    (trans (odd-+ (eval P x y) (eval (μ x[ i ]) x y))
           (cong (odd (eval P x y) xor_) (odd-X i x y)))

  -- The two-variable sums.

  odd-XX : ∀ {n m} (i j : Fin n) (x : Assign n) (y : Assign m) →
           odd (eval (μ x[ i ] +ᴾ μ x[ j ]) x y) ≡ x i xor x j
  odd-XX i j x y = trans (odd-+X (μ x[ i ]) j x y)
                         (cong (_xor x j) (odd-X i x y))


------------------------------------------------------------------------
-- The composite, through its values

-- Along its single path the composite's outputs read cnot₂₃'s at the
-- state cnot₁₂ reaches (proposition 2.7's ingredient, outBit-∘), and
-- that is cnot₁₃'s output, wire by wire.

private
  -- Any path of the composite is the concatenation of the two empty
  -- ones.

  odd-composite : (w : Fin 3) (x : Assign 3) (y : Assign 0) →
                  odd (eval (out composite w) x y) ≡
                  outBit cnot₂₃ (outBit cnot₁₂ x none) none w
  odd-composite w x y = trans
    (cong odd (eval-cong (out composite w) {x} {x} {y} {none ++ᵃ none}
                         (λ _ → refl) (λ ())))
    (outBit-∘ cnot₂₃ cnot₁₂ x none none w)

  -- cnot₁₂ reads x1, x1 ⊕ x2 and x3.

  u₂ : (x : Assign 3) → outBit cnot₁₂ x none (suc zero) ≡ x zero xor x (suc zero)
  u₂ x = odd-XX zero (suc zero) x none

  per-wire : (w : Fin 3) (x : Assign 3) →
             outBit cnot₂₃ (outBit cnot₁₂ x none) none w ≡
             odd (eval (outs₁₃ w) x none)
  per-wire zero x = odd-X zero (outBit cnot₁₂ x none) none
  per-wire (suc zero) x = odd-X (suc zero) (outBit cnot₁₂ x none) none
  per-wire (suc (suc zero)) x = trans
    (odd-XX (suc zero) (suc (suc zero)) (outBit cnot₁₂ x none) none)
    (trans (cong₂ _xor_ (u₂ x) (odd-X (suc (suc zero)) x none))
           (sym (trans (odd-+X (X₁ +ᴾ X₂) (suc (suc zero)) x none)
                       (cong (_xor x (suc (suc zero)))
                             (odd-XX zero (suc zero) x none)))))

  -- cnot₁₃'s outputs take the same values on the empty path, whatever
  -- it is called.

  odd-₁₃ : (w : Fin 3) (x : Assign 3) (y : Assign 0) →
           odd (eval (outs₁₃ w) x none) ≡ odd (eval (outs₁₃ w) x y)
  odd-₁₃ w x y = cong odd (eval-cong (outs₁₃ w) {x} {x} {none} {y}
                                     (λ _ → refl) (λ ()))

-- The outputs agree coefficient by coefficient modulo 2.

composite-outs : ∀ w → out composite w ≈[ + 2 ] outs₁₃ w
composite-outs w = ≈-from-values (out composite w) (outs₁₃ w) (λ x y →
  odd-≡ (eval (out composite w) x y) (eval (outs₁₃ w) x y)
    (trans (odd-composite w x y) (trans (per-wire w x) (odd-₁₃ w x y))))

-- The phase is 0 + 0 at every point (eval-∘), so 0 coefficient by
-- coefficient modulo 1.

composite-phase : phase composite ≈[ pow 3 ] 0ᴾ
composite-phase = ≈-from-values (phase composite) 0ᴾ (λ x y →
  subst (pow 3 ∣_) (sym (value x y)) i∣0)
  where
  value : (x : Assign 3) (y : Assign 0) →
          eval (phase composite) x y - eval (0ᴾ {3} {0}) x y ≡ 0ℤ
  value x y = trans
    (cong₂ _-_
      (trans (eval-cong (phase composite) {x} {x} {y} {none ++ᵃ none}
                        (λ _ → refl) (λ ()))
        (trans (eval-∘ cnot₂₃ cnot₁₂ x none none)
          (cong₂ _+_ (eval-0ᴾ x none) (eval-0ᴾ (outBit cnot₁₂ x none) none))))
      (eval-0ᴾ x y))
    refl

-- So the composite is the paper's |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3)⟩,
-- syntactically, and hence equivalent to it.

composite-congruent : Congruent composite cnot₁₃
composite-congruent = composite-outs , composite-phase

composite-≋ : composite ≋ cnot₁₃
composite-≋ = congruent-≋ composite cnot₁₃ refl composite-congruent


------------------------------------------------------------------------
-- The lifting of x ⊕ y

-- The Boolean polynomial x ⊕ y, read modulo 2, in the inputs x and y.

xorᴾ : Poly 2 0
xorᴾ = μ x[ zero ] +ᴾ μ x[ suc zero ]

-- The monomial xy.

xy : Mon 2 0
xy = inside ∷ inside ∷ [] , []

-- The values: ¼(x ⊕ y) = ¼x + ¼y − ½xy for all x, y ∈ Z₂.

lift-instance-values : ∀ (a b : Bool) →
  ¼ * [ a xor b ]ᶻ ≡ (¼ * [ a ]ᶻ + ¼ * [ b ]ᶻ) - ½ * ([ a ]ᶻ * [ b ]ᶻ)
lift-instance-values false false = refl
lift-instance-values false true  = refl
lift-instance-values true  false = refl
lift-instance-values true  true  = refl

-- The lift of x ⊕ y is x + y − 2xy, coefficient by coefficient.

lift-xor : ∀ γ → liftᴮ xorᴾ γ ≡
                 ((μ x[ zero ] +ᴾ μ x[ suc zero ]) -ᴾ (+ 2) ·ᴾ monoᴾ xy) γ
lift-xor (outside ∷ outside ∷ [] , []) = refl
lift-xor (outside ∷ inside  ∷ [] , []) = refl
lift-xor (inside  ∷ outside ∷ [] , []) = refl
lift-xor (inside  ∷ inside  ∷ [] , []) = refl

-- Hence ¼ times it is ¼x + ¼y − ½xy, coefficient by coefficient.

lift-instance : ∀ γ →
  (¼ ·ᴾ liftᴮ xorᴾ) γ ≡
  ((¼ ·ᴾ μ x[ zero ] +ᴾ ¼ ·ᴾ μ x[ suc zero ]) -ᴾ ½ ·ᴾ monoᴾ xy) γ
lift-instance (outside ∷ outside ∷ [] , []) = refl
lift-instance (outside ∷ inside  ∷ [] , []) = refl
lift-instance (inside  ∷ outside ∷ [] , []) = refl
lift-instance (inside  ∷ inside  ∷ [] , []) = refl
