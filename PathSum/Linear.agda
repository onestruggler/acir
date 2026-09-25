------------------------------------------------------------------------
-- Presentations of groups
--
-- Z₂-linear forms and the value of their lifting (Amy, QPL 2018,
-- lemma 2.5 for linear forms)
--
-- Over the gates H, CNOT and R_k every wire of a circuit holds a
-- Z₂-linear form  c ⊕ ⨁_{u ∈ S} u  in the input and path variables:
-- a Hadamard puts a fresh variable on its wire and CNOT adds the form
-- on its control to the form on its target.  Such a form is a pair
-- Lin n m = Bool × Mon n m, and valᴸ is its value at an assignment.
-- The phase and the output polynomials of a path-sum do not hold the
-- form itself but its lifting to D, liftXor c S of PathSum.Polynomial,
-- the polynomial  c + (1 - 2c) Σ_{∅ ≠ γ ⊆ S} (-2)^(|γ|-1) x^γ.
--
-- Lemma 2.5 says that lifting preserves the values of a Boolean
-- polynomial.  PathSum.Polynomial.Properties.liftXor-value proves only
-- that the lifting of a linear form is 0 or 1 at every point; here
-- eval-liftXor proves which, [ c ⊕ ⨁_{u ∈ S} u ]ᶻ, by induction on the
-- size of S, peeling off one variable at a time with
-- Properties.liftXor-split.  Only linear forms are treated: the lemma
-- for an arbitrary Boolean polynomial would need products of lifted
-- polynomials, which nothing here uses.
--
-- The outputs of such a circuit are therefore linear in the sense of
-- section 2.2: every coefficient of degree at least 2 of the lifting
-- is even (liftXor-linear), so modulo 2 only the constant and the
-- linear terms survive.
--
-- Two operations on polynomials that the Hadamard gate needs are here
-- too: wkLin, a form read with one more path variable at the head, and
-- mul-y₀, the product of a polynomial with that fresh variable -- the
-- only product of polynomials definition 2.9 ever forms.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Linear where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Bool.Properties using
  (xor-assoc; xor-comm; xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⁅_⁆; ⊥; _∈_; ∣_∣)
  renaming (_-_ to _∖_)
open import Data.Fin.Subset.Properties using (∉⊥; p─⊥≡p; x∈p⇒∣p-x∣<∣p∣)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣-trans)
open import Data.Nat.Base using (ℕ; zero; suc; _∸_; _≤_; _<_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_; here; there; zipWith)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; ⟪_⟫; ∥_∥; _∈ᵐ_; _∖ᵐ_; eval; liftXor)
open import PathSum.Polynomial.Properties using
  (valᵛ; emptyᵇ; emptyᵐ; emptyᵇ⇒≡⊥; emptyᵇ-witness; emptyᵐ-false;
   liftXor-off; liftXor-split; liftXor-∣; 2^-mono-∣)

import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- Parities

-- The parity of the elements of a subset that an assignment makes
-- true, defined like PathSum.Polynomial.sat, with _xor_ for _∧_.

par : Subset k → (Fin k → Bool) → Bool
par []            f = false
par (inside  ∷ p) f = f zero xor par p (λ i → f (suc i))
par (outside ∷ p) f = par p (λ i → f (suc i))

parᵐ : Mon n m → (Fin n → Bool) → (Fin m → Bool) → Bool
parᵐ (α , β) x y = par α x xor par β y


------------------------------------------------------------------------
-- Linear forms

-- The form  c ⊕ ⨁_{u ∈ S} u.

Lin : ℕ → ℕ → Set
Lin n m = Bool × Mon n m

valᴸ : Lin n m → (Fin n → Bool) → (Fin m → Bool) → Bool
valᴸ (c , S) x y = c xor parᵐ S x y

-- Its lifting to a polynomial over D.

liftᴸ : Lin n m → Poly n m
liftᴸ (c , S) = liftXor c S

-- A single variable.

varᴸ : Var n m → Lin n m
varᴸ v = false , ⟪ v ⟫

-- The sum of two forms: the symmetric difference of their sets.

infixl 6 _⊕ᵐ_ _⊕ᴸ_

_⊕ᵐ_ : Mon n m → Mon n m → Mon n m
(α , β) ⊕ᵐ (α′ , β′) = zipWith _xor_ α α′ , zipWith _xor_ β β′

_⊕ᴸ_ : Lin n m → Lin n m → Lin n m
(c , S) ⊕ᴸ (c′ , S′) = c xor c′ , S ⊕ᵐ S′

-- A form read with one more path variable, taken at the head, as
-- PathSum.Circuit's wkPoly does for polynomials.

wkLin : Lin n m → Lin n (suc m)
wkLin (c , (α , β)) = c , (α , outside ∷ β)

-- The product of a polynomial with the fresh head path variable y₀:
-- head-part (mul-y₀ P) is P and tail-part (mul-y₀ P) is 0, both
-- definitionally.

mul-y₀ : Poly n m → Poly n (suc m)
mul-y₀ P (α , inside  ∷ β) = P (α , β)
mul-y₀ P (α , outside ∷ β) = 0ℤ


------------------------------------------------------------------------
-- Properties of parities

private
  xor-left-comm : ∀ a b c → a xor (b xor c) ≡ b xor (a xor c)
  xor-left-comm a b c = trans (sym (xor-assoc a b c))
    (trans (cong (_xor c) (xor-comm a b)) (xor-assoc b a c))

  xor-right-comm : ∀ a b c → (a xor b) xor c ≡ (a xor c) xor b
  xor-right-comm a b c = trans (xor-assoc a b c)
    (trans (cong (a xor_) (xor-comm b c)) (sym (xor-assoc a c b)))

  xor-medial : ∀ a b c d →
               (a xor b) xor (c xor d) ≡ (a xor c) xor (b xor d)
  xor-medial a b c d = trans (xor-assoc a b (c xor d))
    (trans (cong (a xor_) (xor-left-comm b c d))
           (sym (xor-assoc a c (b xor d))))

-- A parity reads the assignment only through its values.

par-cong : (p : Subset k) {f g : Fin k → Bool} → (∀ i → f i ≡ g i) →
           par p f ≡ par p g
par-cong []            f≗g = refl
par-cong (inside  ∷ p) f≗g =
  cong₂ _xor_ (f≗g zero) (par-cong p (λ i → f≗g (suc i)))
par-cong (outside ∷ p) f≗g = par-cong p (λ i → f≗g (suc i))

-- The empty set and the singletons.

par-⊥ : (f : Fin k → Bool) → par (⊥ {k}) f ≡ false
par-⊥ {k = zero}  f = refl
par-⊥ {k = suc k} f = par-⊥ (λ i → f (suc i))

par-⁅⁆ : (i : Fin k) (f : Fin k → Bool) → par ⁅ i ⁆ f ≡ f i
par-⁅⁆ zero    f = trans (cong (f zero xor_) (par-⊥ (λ i → f (suc i))))
                         (xor-identityʳ (f zero))
par-⁅⁆ (suc i) f = par-⁅⁆ i (λ j → f (suc j))

par-empty : (p : Subset k) (f : Fin k → Bool) → emptyᵇ p ≡ true →
            par p f ≡ false
par-empty []            f _  = refl
par-empty (inside  ∷ p) f ()
par-empty (outside ∷ p) f eq = par-empty p (λ i → f (suc i)) eq

-- Removing an element of the set removes its value from the parity.

par-∖ : {p : Subset k} {i : Fin k} (f : Fin k → Bool) → i ∈ p →
        par p f ≡ par (p ∖ i) f xor f i
par-∖ {p = inside ∷ p} f here = trans
  (xor-comm (f zero) (par p (λ j → f (suc j))))
  (cong (λ q → par q (λ j → f (suc j)) xor f zero) (sym (p─⊥≡p p)))
par-∖ {p = inside ∷ p} {suc i} f (there i∈p) = trans
  (cong (f zero xor_) (par-∖ (λ j → f (suc j)) i∈p))
  (sym (xor-assoc (f zero) (par (p ∖ i) (λ j → f (suc j))) (f (suc i))))
par-∖ {p = outside ∷ p} {suc i} f (there i∈p) =
  par-∖ (λ j → f (suc j)) i∈p

-- The parity of a symmetric difference is the sum of the parities.

par-⊕ : (p q : Subset k) (f : Fin k → Bool) →
        par (zipWith _xor_ p q) f ≡ par p f xor par q f
par-⊕ []            []            f = refl
par-⊕ (inside  ∷ p) (inside  ∷ q) f = trans
  (par-⊕ p q (λ i → f (suc i)))
  (sym (trans (xor-medial (f zero) (par p (λ i → f (suc i)))
                          (f zero) (par q (λ i → f (suc i))))
              (cong (_xor (par p (λ i → f (suc i)) xor
                           par q (λ i → f (suc i))))
                    (xor-same (f zero)))))
par-⊕ (inside  ∷ p) (outside ∷ q) f = trans
  (cong (f zero xor_) (par-⊕ p q (λ i → f (suc i))))
  (sym (xor-assoc (f zero) (par p (λ i → f (suc i)))
                  (par q (λ i → f (suc i)))))
par-⊕ (outside ∷ p) (inside  ∷ q) f = trans
  (cong (f zero xor_) (par-⊕ p q (λ i → f (suc i))))
  (xor-left-comm (f zero) (par p (λ i → f (suc i)))
                 (par q (λ i → f (suc i))))
par-⊕ (outside ∷ p) (outside ∷ q) f = par-⊕ p q (λ i → f (suc i))

-- Removing a variable from a monomial.

parᵐ-∖ : (S : Mon n m) (v : Var n m) (x : Fin n → Bool) (y : Fin m → Bool) →
         v ∈ᵐ S → parᵐ S x y ≡ parᵐ (S ∖ᵐ v) x y xor valᵛ v x y
parᵐ-∖ (α , β) x[ i ] x y i∈α = trans
  (cong (_xor par β y) (par-∖ x i∈α))
  (xor-right-comm (par (α ∖ i) x) (x i) (par β y))
parᵐ-∖ (α , β) y[ j ] x y j∈β = trans
  (cong (par α x xor_) (par-∖ y j∈β))
  (sym (xor-assoc (par α x) (par (β ∖ j) y) (y j)))


------------------------------------------------------------------------
-- Values of linear forms

valᴸ-var : (v : Var n m) (x : Fin n → Bool) (y : Fin m → Bool) →
           valᴸ (varᴸ v) x y ≡ valᵛ v x y
valᴸ-var x[ i ] x y =
  trans (cong₂ _xor_ (par-⁅⁆ i x) (par-⊥ y)) (xor-identityʳ (x i))
valᴸ-var y[ j ] x y = cong₂ _xor_ (par-⊥ x) (par-⁅⁆ j y)

valᴸ-⊕ : (l l′ : Lin n m) (x : Fin n → Bool) (y : Fin m → Bool) →
         valᴸ (l ⊕ᴸ l′) x y ≡ (valᴸ l x y xor valᴸ l′ x y)
valᴸ-⊕ (c , α , β) (c′ , α′ , β′) x y = trans
  (cong ((c xor c′) xor_)
    (trans (cong₂ _xor_ (par-⊕ α α′ x) (par-⊕ β β′ y))
           (xor-medial (par α x) (par α′ x) (par β y) (par β′ y))))
  (sym (xor-medial c (par α x xor par β y) c′ (par α′ x xor par β′ y)))

-- A weakened form ignores the fresh head variable.

valᴸ-wk : (l : Lin n m) (x : Fin n → Bool) (y : Fin m → Bool)
          (y′ : Fin (suc m) → Bool) → (∀ j → y′ (suc j) ≡ y j) →
          valᴸ (wkLin l) x y′ ≡ valᴸ l x y
valᴸ-wk (c , α , β) x y y′ h =
  cong (λ b → c xor (par α x xor b)) (par-cong β h)


------------------------------------------------------------------------
-- Lemma 2.5 for linear forms

-- A non-empty monomial has a variable in it.

private
  witness : (S : Mon n m) → emptyᵐ S ≡ false → ∃ λ v → v ∈ᵐ S
  witness (α , β) ne with emptyᵇ α in eα
  ... | false = x[ proj₁ w ] , proj₂ w
    where
    w = emptyᵇ-witness α eα
  ... | true  = y[ proj₁ w ] , proj₂ w
    where
    w = emptyᵇ-witness β ne

  ∧-true : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true true  true  _ = refl , refl
  ∧-true true  false ()
  ∧-true false _     ()

  -- Removing a variable makes a monomial smaller.

  ∥∖ᵐ∥< : (S : Mon n m) (v : Var n m) → v ∈ᵐ S → ∥ S ∖ᵐ v ∥ < ∥ S ∥
  ∥∖ᵐ∥< (α , β) x[ i ] i∈α = ℕ.+-monoˡ-< ∣ β ∣ (x∈p⇒∣p-x∣<∣p∣ i∈α)
  ∥∖ᵐ∥< (α , β) y[ j ] j∈β = ℕ.+-monoʳ-< ∣ α ∣ (x∈p⇒∣p-x∣<∣p∣ j∈β)

  -- The recursion of section 2,  P ⊕ Q  lifted to  P + Q - 2PQ,  at
  -- one variable.

  lift-step : ∀ a b → [ a ]ᶻ + [ b ]ᶻ * (1ℤ - (+ 2) * [ a ]ᶻ) ≡
                      [ a xor b ]ᶻ
  lift-step false false = refl
  lift-step false true  = refl
  lift-step true  false = refl
  lift-step true  true  = refl

-- The value of the lifting, by induction on the size of the set.  An
-- empty set leaves the constant; otherwise liftXor-split removes one
-- variable v, and the recursion above adds its value back.

private
  module Value {n m : ℕ} (c : Bool) (x : Fin n → Bool) (y : Fin m → Bool)
    where

    empty-case : (S : Mon n m) → emptyᵐ S ≡ true →
                 eval (liftXor c S) x y ≡ [ c xor parᵐ S x y ]ᶻ
    empty-case (α , β) e = trans
      (liftXor-off c (α , β) x y
        (λ j j∈α → contradiction (Eq.subst (j ∈_) (emptyᵇ⇒≡⊥ α eα) j∈α) ∉⊥)
        (λ j j∈β → contradiction (Eq.subst (j ∈_) (emptyᵇ⇒≡⊥ β eβ) j∈β) ∉⊥))
      (cong [_]ᶻ (sym (trans
        (cong (c xor_) (cong₂ _xor_ (par-empty α x eα) (par-empty β y eβ)))
        (xor-identityʳ c))))
      where
      eα = proj₁ (∧-true (emptyᵇ α) (emptyᵇ β) e)
      eβ = proj₂ (∧-true (emptyᵇ α) (emptyᵇ β) e)

    mutual
      go : ∀ fuel (S : Mon n m) → ∥ S ∥ ≤ fuel →
           eval (liftXor c S) x y ≡ [ c xor parᵐ S x y ]ᶻ
      go fuel S le = by-empty fuel S le (emptyᵐ S) refl

      by-empty : ∀ fuel (S : Mon n m) → ∥ S ∥ ≤ fuel → ∀ b → emptyᵐ S ≡ b →
                 eval (liftXor c S) x y ≡ [ c xor parᵐ S x y ]ᶻ
      by-empty fuel       S le true  e = empty-case S e
      by-empty zero       S le false e = contradiction
        (ℕ.≤-trans (ℕ.≤-reflexive (sym (emptyᵐ-false S e))) le) λ ()
      by-empty (suc fuel) S le false e = trans
        (liftXor-split c S v v∈S x y)
        (trans
          (cong (λ q → q + ([ valᵛ v x y ]ᶻ * (1ℤ - (+ 2) * q))) ih)
          (trans (lift-step (c xor parᵐ (S ∖ᵐ v) x y) (valᵛ v x y))
                 (cong [_]ᶻ (trans
                   (xor-assoc c (parᵐ (S ∖ᵐ v) x y) (valᵛ v x y))
                   (cong (c xor_) (sym (parᵐ-∖ S v x y v∈S)))))))
        where
        v   = proj₁ (witness S e)
        v∈S = proj₂ (witness S e)

        ih : eval (liftXor c (S ∖ᵐ v)) x y ≡
             [ c xor parᵐ (S ∖ᵐ v) x y ]ᶻ
        ih = go fuel (S ∖ᵐ v)
          (ℕ.≤-pred (ℕ.≤-trans (∥∖ᵐ∥< S v v∈S) le))

-- Lemma 2.5, with the value.

eval-liftXor : (c : Bool) (S : Mon n m) (x : Fin n → Bool)
               (y : Fin m → Bool) →
               eval (liftXor c S) x y ≡ [ c xor parᵐ S x y ]ᶻ
eval-liftXor c S x y = Value.go c x y ∥ S ∥ S ℕ.≤-refl

eval-liftᴸ : (l : Lin n m) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (liftᴸ l) x y ≡ [ valᴸ l x y ]ᶻ
eval-liftᴸ (c , S) x y = eval-liftXor c S x y


------------------------------------------------------------------------
-- Liftings are linear modulo 2

-- Every coefficient of degree at least 2 is divisible by
-- 2^(|γ| - 1), and so is even.

liftXor-linear : (c : Bool) (S γ : Mon n m) → 2 ≤ ∥ γ ∥ →
                 (+ 2) ∣ liftXor c S γ
liftXor-linear c S γ 2≤γ =
  ∣-trans (2^-mono-∣ (ℕ.∸-monoˡ-≤ 1 2≤γ)) (liftXor-∣ c S γ)
