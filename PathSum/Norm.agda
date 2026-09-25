------------------------------------------------------------------------
-- Presentations of groups
--
-- The trace norm on Z[ζ]
--
-- Lemma 4.1 needs to measure an amplitude, and the measure it needs is
-- the squared norm ‖a‖² = Σᵢ aᵢ², the sum of the squares of the
-- coordinates of a in the basis ζ^0 … ζ^(H-1).  Up to the factor H it
-- is the trace of a·ā from Q(ζ) to Q, the sum of |σ(a)|² over the
-- embeddings σ, and that is why it has the two properties the lemma
-- uses: it is positive definite, and multiplying by a power of ζ
-- preserves it.  The first is a fact about sums of squares.  The
-- second is proved by reading the form through `coeff` rather than
-- through the coordinates: a rotation only shifts the exponent, so it
-- shifts the window of H consecutive exponents the form sums over,
-- and a window can be moved freely because the summand -- a product
-- of two coefficients, each changing sign under ζ^H = -1 -- is
-- periodic with period H.
--
-- The rest follows by algebra: the parallelogram law, √2 doubling the
-- norm (the cross term of ζ^c and ζ^(-c) vanishes because
-- multiplication by ζ^(2c) = i is antisymmetric for the form), and
-- ζ^0 being a unit vector.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Norm (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_; _≤_; +≤+; ∣_∣; +0; +[1+_]; -[1+_])
open import Data.Integer.Divisibility.Signed using (_∣_; ∣⇒∣ᵤ; ∣ᵤ⇒∣)
open import Data.Integer.Properties using
  (+-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ;
   neg-involutive; neg-distrib-+; neg-distribʳ-*; *-comm; *-assoc;
   *-identityˡ; *-zeroʳ; *-distribˡ-+; *-cancelˡ-≡; pos-*; ≤-refl;
   ≤-trans; ≤-reflexive; ≤-antisym; +-mono-≤; +-monoʳ-≤;
   i*j≡0⇒i≡0∨j≡0; ∣-i∣≡∣i∣)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _<_; s≤s; z≤n)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _^_ to _ℕ^_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Cyclotomic M₀

import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)


------------------------------------------------------------------------
-- Sums over a window

-- The sum f 0 + … + f (k-1), by recursion on the last term.

Σ< : ℕ → (ℕ → ℤ) → ℤ
Σ< zero    f = 0ℤ
Σ< (suc k) f = Σ< k f + f k

-- Linearity.

Σ<-cong : ∀ k {f g : ℕ → ℤ} → (∀ j → f j ≡ g j) → Σ< k f ≡ Σ< k g
Σ<-cong zero    eq = refl
Σ<-cong (suc k) eq = cong₂ _+_ (Σ<-cong k eq) (eq k)

Σ<-+ : ∀ k (f g : ℕ → ℤ) → Σ< k (λ j → f j + g j) ≡ Σ< k f + Σ< k g
Σ<-+ zero    f g = refl
Σ<-+ (suc k) f g = trans (cong (_+ (f k + g k)) (Σ<-+ k f g))
                         (shuffle (Σ< k f) (Σ< k g) (f k) (g k))
  where
  shuffle : ∀ p q r t → (p + q) + (r + t) ≡ (p + r) + (q + t)
  shuffle = solve 4 (λ p q r t →
    (p :+ q) :+ (r :+ t) := (p :+ r) :+ (q :+ t)) refl

Σ<-* : ∀ k (z : ℤ) (f : ℕ → ℤ) → Σ< k (λ j → z * f j) ≡ z * Σ< k f
Σ<-* zero    z f = sym (*-zeroʳ z)
Σ<-* (suc k) z f = trans (cong (_+ (z * f k)) (Σ<-* k z f))
                         (sym (*-distribˡ-+ z (Σ< k f) (f k)))

Σ<-neg : ∀ k (f : ℕ → ℤ) → Σ< k (λ j → - f j) ≡ - Σ< k f
Σ<-neg zero    f = refl
Σ<-neg (suc k) f = trans (cong (_+ (- f k)) (Σ<-neg k f))
                         (sym (neg-distrib-+ (Σ< k f) (f k)))

-- A sum whose terms vanish on the window vanishes, and a sum can be
-- split at its first term instead of its last.

Σ<-0 : ∀ k {f : ℕ → ℤ} → (∀ j → j < k → f j ≡ 0ℤ) → Σ< k f ≡ 0ℤ
Σ<-0 zero    _ = refl
Σ<-0 (suc k) z = cong₂ _+_
  (Σ<-0 k (λ j j<k → z j (ℕ.<-trans j<k (ℕ.n<1+n k))))
  (z k (ℕ.n<1+n k))

Σ<-front : ∀ k (f : ℕ → ℤ) → Σ< (suc k) f ≡ f 0 + Σ< k (λ j → f (suc j))
Σ<-front zero    f = +-comm 0ℤ (f 0)
Σ<-front (suc k) f = trans (cong (_+ f (suc k)) (Σ<-front k f))
  (+-assoc (f 0) (Σ< k (λ j → f (suc j))) (f (suc k)))

-- Sums of non-negative terms: they are non-negative, and they vanish
-- only when every term does.

private
  -- Two non-negative integers summing to zero are both zero.

  left0 : ∀ {x y} → 0ℤ ≤ x → 0ℤ ≤ y → x + y ≡ 0ℤ → x ≡ 0ℤ
  left0 {x} {y} 0≤x 0≤y eq = ≤-antisym
    (≤-trans (≤-reflexive (sym (+-identityʳ x)))
             (≤-trans (+-monoʳ-≤ x 0≤y) (≤-reflexive eq)))
    0≤x

  right0 : ∀ {x y} → 0ℤ ≤ x → 0ℤ ≤ y → x + y ≡ 0ℤ → y ≡ 0ℤ
  right0 {x} {y} 0≤x 0≤y eq = left0 0≤y 0≤x (trans (+-comm y x) eq)

Σ<-≥0 : ∀ k (f : ℕ → ℤ) → (∀ j → 0ℤ ≤ f j) → 0ℤ ≤ Σ< k f
Σ<-≥0 zero    f nn = ≤-refl
Σ<-≥0 (suc k) f nn = +-mono-≤ (Σ<-≥0 k f nn) (nn k)

Σ<-≡0 : ∀ k (f : ℕ → ℤ) → (∀ j → 0ℤ ≤ f j) → Σ< k f ≡ 0ℤ →
        ∀ j → j < k → f j ≡ 0ℤ
Σ<-≡0 zero    f nn eq j ()
Σ<-≡0 (suc k) f nn eq j j<1+k with ℕ.m<1+n⇒m<n∨m≡n j<1+k
... | inj₁ j<k  = Σ<-≡0 k f nn (left0 (Σ<-≥0 k f nn) (nn k) eq) j j<k
... | inj₂ refl = right0 (Σ<-≥0 k f nn) (nn k) eq


------------------------------------------------------------------------
-- Coefficients

-- A coefficient read at an exponent congruent to a basis exponent,
-- or to one shifted by H.

coeff-at⁺ : ∀ a w (i : Fin H) → (+ N) ∣ (w - (+ toℕ i)) → coeff a w ≡ a i
coeff-at⁺ a w i d = trans (coeff-cong a w (+ toℕ i) d) (coeff-δ a i)

coeff-at⁻ : ∀ a w (i : Fin H) → (+ N) ∣ (w - ((+ toℕ i) + (+ H))) →
            coeff a w ≡ - a i
coeff-at⁻ a w i d = trans (coeff-cong a w ((+ toℕ i) + (+ H)) d)
  (trans (coeff-anti a (+ toℕ i)) (cong -_ (coeff-δ a i)))

-- Rotating by ζ^e shifts every coefficient by e, not only the ones in
-- the basis window.

coeff-rot : ∀ e a w → coeff (rot e a) w ≡ coeff a (w - e)
coeff-rot e a w = go (classify w)
  where
  go : Class w → coeff (rot e a) w ≡ coeff a (w - e)
  go (pos i d) = trans (coeff-at⁺ (rot e a) w i d)
    (sym (coeff-cong a (w - e) ((+ toℕ i) - e)
      (subst ((+ N) ∣_) (shape w (+ toℕ i) e) d)))
    where
    shape : ∀ u v t → u - v ≡ (u - t) - (v - t)
    shape = solve 3 (λ u v t → u :- v := (u :- t) :- (v :- t)) refl
  go (neg i d) = trans (coeff-at⁻ (rot e a) w i d)
    (sym (trans (coeff-cong a (w - e) (((+ toℕ i) - e) + (+ H))
                  (subst ((+ N) ∣_) (shape w (+ toℕ i) e (+ H)) d))
                (coeff-anti a ((+ toℕ i) - e))))
    where
    shape : ∀ u v t s → u - (v + s) ≡ (u - t) - ((v - t) + s)
    shape = solve 4 (λ u v t s →
      u :- (v :+ s) := (u :- t) :- ((v :- t) :+ s)) refl

-- Coefficients of the other ring operations.

coeff-neg : ∀ a w → coeff (-ᴬ a) w ≡ - coeff a w
coeff-neg a w = go (classify w)
  where
  go : Class w → coeff (-ᴬ a) w ≡ - coeff a w
  go (pos i d) =
    trans (coeff-at⁺ (-ᴬ a) w i d) (cong -_ (sym (coeff-at⁺ a w i d)))
  go (neg i d) =
    trans (coeff-at⁻ (-ᴬ a) w i d) (cong -_ (sym (coeff-at⁻ a w i d)))

coeff-sub : ∀ a b w → coeff (a -ᴬ b) w ≡ coeff a w - coeff b w
coeff-sub a b w =
  trans (coeff-+ a (-ᴬ b) w) (cong (λ u → coeff a w + u) (coeff-neg b w))

coeff-0ᴬ : ∀ w → coeff 0ᴬ w ≡ 0ℤ
coeff-0ᴬ w = go (classify w)
  where
  go : Class w → coeff 0ᴬ w ≡ 0ℤ
  go (pos i d) = coeff-at⁺ 0ᴬ w i d
  go (neg i d) = coeff-at⁻ 0ᴬ w i d


------------------------------------------------------------------------
-- The trace form

-- ⟪a , b⟫ sums the products of coefficients over the basis window.

⟪_,_⟫ : Amp → Amp → ℤ
⟪ a , b ⟫ = Σ< H (λ j → coeff a (+ j) * coeff b (+ j))

‖_‖² : Amp → ℤ
‖ a ‖² = ⟪ a , a ⟫

⟪⟫-cong : ∀ {a a′ b b′} → a ≐ a′ → b ≐ b′ → ⟪ a , b ⟫ ≡ ⟪ a′ , b′ ⟫
⟪⟫-cong a≐a′ b≐b′ = Σ<-cong H (λ j →
  cong₂ _*_ (coeff-map a≐a′ (+ j)) (coeff-map b≐b′ (+ j)))

‖‖²-cong : ∀ {a b} → a ≐ b → ‖ a ‖² ≡ ‖ b ‖²
‖‖²-cong a≐b = ⟪⟫-cong a≐b a≐b

⟪⟫-comm : ∀ a b → ⟪ a , b ⟫ ≡ ⟪ b , a ⟫
⟪⟫-comm a b = Σ<-cong H (λ j → *-comm (coeff a (+ j)) (coeff b (+ j)))

⟪⟫-negʳ : ∀ a b → ⟪ a , -ᴬ b ⟫ ≡ - ⟪ a , b ⟫
⟪⟫-negʳ a b = trans
  (Σ<-cong H (λ j → trans (cong (coeff a (+ j) *_) (coeff-neg b (+ j)))
                          (sym (neg-distribʳ-* (coeff a (+ j))
                                               (coeff b (+ j))))))
  (Σ<-neg H (λ j → coeff a (+ j) * coeff b (+ j)))

-- The norm of a sum, expanded.

‖‖²-+ : ∀ u v → ‖ u +ᴬ v ‖² ≡ (‖ u ‖² + (+ 2) * ⟪ u , v ⟫) + ‖ v ‖²
‖‖²-+ u v = trans (Σ<-cong H pt)
  (trans (Σ<-+ H (λ j → uu j + (+ 2) * uv j) vv)
    (cong (_+ ‖ v ‖²)
      (trans (Σ<-+ H uu (λ j → (+ 2) * uv j))
             (cong (λ x → ‖ u ‖² + x) (Σ<-* H (+ 2) uv)))))
  where
  p q uu uv vv : ℕ → ℤ
  p j  = coeff u (+ j)
  q j  = coeff v (+ j)
  uu j = p j * p j
  uv j = p j * q j
  vv j = q j * q j

  expand : ∀ x y → (x + y) * (x + y) ≡ ((x * x) + (+ 2) * (x * y)) + y * y
  expand = solve 2 (λ x y → (x :+ y) :* (x :+ y) :=
    ((x :* x) :+ (con (+ 2) :* (x :* y))) :+ (y :* y)) refl

  pt : ∀ j → coeff (u +ᴬ v) (+ j) * coeff (u +ᴬ v) (+ j) ≡
             (uu j + (+ 2) * uv j) + vv j
  pt j = trans (cong₂ _*_ (coeff-+ u v (+ j)) (coeff-+ u v (+ j)))
               (expand (p j) (q j))


------------------------------------------------------------------------
-- Positive definiteness

-- Squares are non-negative, and only 0 squares to 0.

sq≥0 : ∀ x → 0ℤ ≤ x * x
sq≥0 +0         = +≤+ z≤n
sq≥0 +[1+ n ]   = +≤+ z≤n
sq≥0 -[1+ n ]   = +≤+ z≤n

private
  sq≡0 : ∀ x → x * x ≡ 0ℤ → x ≡ 0ℤ
  sq≡0 x eq with i*j≡0⇒i≡0∨j≡0 x eq
  ... | inj₁ x≡0 = x≡0
  ... | inj₂ x≡0 = x≡0

‖‖²-≥0 : ∀ a → 0ℤ ≤ ‖ a ‖²
‖‖²-≥0 a = Σ<-≥0 H (λ j → coeff a (+ j) * coeff a (+ j))
                   (λ j → sq≥0 (coeff a (+ j)))

-- A coordinate i of a is its coefficient at an exponent inside the
-- window, so a zero norm kills it.

‖‖²-zero : ∀ a → ‖ a ‖² ≡ 0ℤ → a ≐ 0ᴬ
‖‖²-zero a eq i = trans (sym (coeff-δ a i)) (sq≡0 (coeff a (+ toℕ i))
  (Σ<-≡0 H (λ j → coeff a (+ j) * coeff a (+ j))
         (λ j → sq≥0 (coeff a (+ j))) eq (toℕ i) (toℕ<n i)))

‖0ᴬ‖² : ‖ 0ᴬ ‖² ≡ 0ℤ
‖0ᴬ‖² = Σ<-0 H (λ j _ → cong₂ _*_ (coeff-0ᴬ (+ j)) (coeff-0ᴬ (+ j)))


------------------------------------------------------------------------
-- Multiplication by a power of ζ is an isometry

-- The window of summation can be moved.  Sliding it up by one trades
-- the term at its bottom for the term just above its top, H further
-- on, and for an H-periodic summand the two are equal.  Sliding it
-- repeatedly moves it anywhere.

module Window (g : ℤ → ℤ) (per : ∀ w → g (w + (+ H)) ≡ g w) where

  T : ℕ → ℤ → ℤ
  T k s = Σ< k (λ j → g ((+ j) + s))

  slide : ∀ k s → T k (s + 1ℤ) + g s ≡ T k s + g ((+ k) + s)
  slide zero    s = cong (λ u → 0ℤ + g u) (sym (+-identityˡ s))
  slide (suc k) s = trans
    (swap (T k (s + 1ℤ)) (g ((+ k) + (s + 1ℤ))) (g s))
    (cong₂ _+_ (slide k s) (cong g (shift (+ k) s)))
    where
    swap : ∀ x y z → (x + y) + z ≡ (x + z) + y
    swap = solve 3 (λ x y z → (x :+ y) :+ z := (x :+ z) :+ y) refl

    -- 1ℤ + + k is + suc k by computation.
    shift : ∀ x u → x + (u + 1ℤ) ≡ (1ℤ + x) + u
    shift = solve 2 (λ x u →
      x :+ (u :+ con 1ℤ) := (con 1ℤ :+ x) :+ u) refl

  cancelʳ : ∀ {x y} z → x + z ≡ y + z → x ≡ y
  cancelʳ {x} {y} z eq =
    trans (sym (drop x z)) (trans (cong (_- z) eq) (drop y z))
    where
    drop : ∀ u v → (u + v) - v ≡ u
    drop = solve 2 (λ u v → (u :+ v) :- v := u) refl

  step : ∀ s → T H (s + 1ℤ) ≡ T H s
  step s = cancelʳ (g s) (trans (slide H s)
    (cong (λ x → T H s + x) (trans (cong g (+-comm (+ H) s)) (per s))))

  climb : ∀ s n → T H (s + (+ n)) ≡ T H s
  climb s zero    = cong (T H) (+-identityʳ s)
  climb s (suc n) = trans (cong (T H) (up s (+ n)))
                          (trans (step (s + (+ n))) (climb s n))
    where
    up : ∀ u x → u + (1ℤ + x) ≡ (u + x) + 1ℤ
    up = solve 2 (λ u x → u :+ (con 1ℤ :+ x) := (u :+ x) :+ con 1ℤ) refl

  window : ∀ s → T H s ≡ T H 0ℤ
  window (+ n)    = climb 0ℤ n
  window -[1+ n ] = sym (trans (cong (T H) (sym (+-inverseˡ (+ suc n))))
                               (climb -[1+ n ] (suc n)))

  rotate : ∀ e → Σ< H (λ j → g ((+ j) - e)) ≡ Σ< H (λ j → g (+ j))
  rotate e =
    trans (window (- e)) (Σ<-cong H (λ j → cong g (+-identityʳ (+ j))))

neg*neg : ∀ x y → (- x) * (- y) ≡ x * y
neg*neg = solve 2 (λ x y → (:- x) :* (:- y) := x :* y) refl

-- The product of two coefficients is H-periodic, both factors
-- changing sign.

⟪⟫-rot : ∀ e a b → ⟪ rot e a , rot e b ⟫ ≡ ⟪ a , b ⟫
⟪⟫-rot e a b = trans
  (Σ<-cong H (λ j → cong₂ _*_ (coeff-rot e a (+ j)) (coeff-rot e b (+ j))))
  (Window.rotate (λ w → coeff a w * coeff b w) per e)
  where
  per : ∀ w → coeff a (w + (+ H)) * coeff b (w + (+ H)) ≡
              coeff a w * coeff b w
  per w = trans (cong₂ _*_ (coeff-anti a w) (coeff-anti b w))
                (neg*neg (coeff a w) (coeff b w))

‖‖²-rot : ∀ e a → ‖ rot e a ‖² ≡ ‖ a ‖²
‖‖²-rot e a = ⟪⟫-rot e a a

‖‖²-neg : ∀ a → ‖ -ᴬ a ‖² ≡ ‖ a ‖²
‖‖²-neg a = Σ<-cong H (λ j →
  trans (cong₂ _*_ (coeff-neg a (+ j)) (coeff-neg a (+ j)))
        (neg*neg (coeff a (+ j)) (coeff a (+ j))))


------------------------------------------------------------------------
-- The parallelogram law

-- What a Hadamard preserves: the norms of a + b and a - b together
-- are twice those of a and b.

parallelogram : ∀ a b →
                ‖ a +ᴬ b ‖² + ‖ a -ᴬ b ‖² ≡ (+ 2) * (‖ a ‖² + ‖ b ‖²)
parallelogram a b = trans (sym (Σ<-+ H sp sm))
  (trans (Σ<-cong H pt)
    (trans (Σ<-* H (+ 2) (λ j → aa j + bb j))
           (cong ((+ 2) *_) (Σ<-+ H aa bb))))
  where
  p q aa bb sp sm : ℕ → ℤ
  p j  = coeff a (+ j)
  q j  = coeff b (+ j)
  aa j = p j * p j
  bb j = q j * q j
  sp j = coeff (a +ᴬ b) (+ j) * coeff (a +ᴬ b) (+ j)
  sm j = coeff (a -ᴬ b) (+ j) * coeff (a -ᴬ b) (+ j)

  law : ∀ x y → (x + y) * (x + y) + (x - y) * (x - y) ≡
                (+ 2) * (x * x + y * y)
  law = solve 2 (λ x y →
    ((x :+ y) :* (x :+ y)) :+ ((x :- y) :* (x :- y)) :=
    con (+ 2) :* ((x :* x) :+ (y :* y))) refl

  pt : ∀ j → sp j + sm j ≡ (+ 2) * (aa j + bb j)
  pt j = trans
    (cong₂ _+_ (cong₂ _*_ (coeff-+ a b (+ j)) (coeff-+ a b (+ j)))
               (cong₂ _*_ (coeff-sub a b (+ j)) (coeff-sub a b (+ j))))
    (law (p j) (q j))


------------------------------------------------------------------------
-- Normalisations

-- ζ^(2c) is i, and multiplying by i is antisymmetric for the form:
-- rotating both sides back by 2c turns ⟪i·a , a⟫ into ⟪a , -i·a⟫,
-- since ζ^(-2c) = -ζ^(2c) when 4c = H.  So ⟪i·a , a⟫ is its own
-- negative.

private
  quarter : ℤ
  quarter = (+ c) + (+ c)

  H≡4c : (+ H) ≡ quarter + quarter
  H≡4c = cong +_ inℕ
    where
    inℕ : H ≡ (c ℕ+ c) ℕ+ (c ℕ+ c)
    inℕ = trans (cong ((2 ℕ* c) ℕ+_) (ℕ.+-identityʳ (2 ℕ* c)))
                (cong₂ _ℕ+_ two two)
      where
      two : 2 ℕ* c ≡ c ℕ+ c
      two = cong (c ℕ+_) (ℕ.+-identityʳ c)

  rot-quarter-anti : ∀ a → rot (- quarter) a ≐ -ᴬ rot quarter a
  rot-quarter-anti a i =
    trans (sym (neg-involutive (rot (- quarter) a i)))
          (cong -_ (sym (trans (rot-exp a turn i)
                               (rot-anti (- quarter) a i))))
    where
    cancel : ∀ u → (- u) + (u + u) ≡ u
    cancel = solve 1 (λ u → (:- u) :+ (u :+ u) := u) refl

    turn : quarter ≡ (- quarter) + (+ H)
    turn = trans (sym (cancel quarter))
                 (cong (λ u → (- quarter) + u) (sym H≡4c))

  self-neg : ∀ {x} → x ≡ - x → x ≡ 0ℤ
  self-neg {x} eq = *-cancelˡ-≡ (+ 2) x 0ℤ
    (trans (twice x) (trans (cong (λ u → x + u) eq) (+-inverseʳ x)))
    where
    twice : ∀ u → (+ 2) * u ≡ u + u
    twice = solve 1 (λ u → con (+ 2) :* u := u :+ u) refl

  ⟪i·a,a⟫ : ∀ a → ⟪ rot quarter a , a ⟫ ≡ 0ℤ
  ⟪i·a,a⟫ a = self-neg (trans (sym (⟪⟫-rot (- quarter) (rot quarter a) a))
    (trans (⟪⟫-cong back (rot-quarter-anti a))
      (trans (⟪⟫-negʳ a (rot quarter a))
             (cong -_ (⟪⟫-comm a (rot quarter a))))))
    where
    back : rot (- quarter) (rot quarter a) ≐ a
    back i = trans (rot-comp (- quarter) quarter a i)
      (trans (rot-exp a (+-inverseˡ quarter) i) (rot-0 a i))

  -- The cross term of √2 · a.

  cross-√2 : ∀ a → ⟪ rot (+ c) a , rot (- (+ c)) a ⟫ ≡ 0ℤ
  cross-√2 a = trans (sym (⟪⟫-rot (+ c) (rot (+ c) a) (rot (- (+ c)) a)))
    (trans (⟪⟫-cong (rot-comp (+ c) (+ c) a) back) (⟪i·a,a⟫ a))
    where
    back : rot (+ c) (rot (- (+ c)) a) ≐ a
    back i = trans (rot-comp (+ c) (- (+ c)) a i)
      (trans (rot-exp a (+-inverseʳ (+ c)) i) (rot-0 a i))

-- √2 · a = ζ^c a + ζ^(-c) a is a sum of two vectors of the norm of a,
-- orthogonal to each other.

‖‖²-√2 : ∀ a → ‖ √2· a ‖² ≡ (+ 2) * ‖ a ‖²
‖‖²-√2 a = trans (‖‖²-+ (rot (+ c) a) (rot (- (+ c)) a))
  (trans (cong₂ _+_ (cong₂ (λ x y → x + (+ 2) * y)
                           (‖‖²-rot (+ c) a) (cross-√2 a))
                    (‖‖²-rot (- (+ c)) a))
         (fold ‖ a ‖²))
  where
  fold : ∀ x → (x + (+ 2) * 0ℤ) + x ≡ (+ 2) * x
  fold = solve 1 (λ x →
    (x :+ (con (+ 2) :* con 0ℤ)) :+ x := con (+ 2) :* x) refl

-- Hence the normalisation √2^j multiplies the norm by 2^j.

‖‖²-scale : ∀ j a → ‖ scale j a ‖² ≡ (+ (2 ℕ^ j)) * ‖ a ‖²
‖‖²-scale zero    a = sym (*-identityˡ ‖ a ‖²)
‖‖²-scale (suc j) a = trans (‖‖²-√2 (scale j a))
  (trans (cong ((+ 2) *_) (‖‖²-scale j a))
    (trans (sym (*-assoc (+ 2) (+ (2 ℕ^ j)) ‖ a ‖²))
           (cong (_* ‖ a ‖²) (sym (pos-* 2 (2 ℕ^ j))))))

-- ζ^0 is a unit vector: its coefficient in the window is 1 at 0 and
-- 0 elsewhere, since for 0 < j < H neither -j nor -j - H is a
-- multiple of N.

H>0 : 0 < H
H>0 = 2^k>0 (2 ℕ+ M₀)
  where
  2^k>0 : ∀ k → 0 < 2 ℕ^ k
  2^k>0 zero    = ℕ.≤-refl
  2^k>0 (suc k) = ℕ.≤-trans (2^k>0 k) (ℕ.m≤m+n (2 ℕ^ k) _)

private
  H<N : H < N
  H<N = ℕ.m<m+n H (ℕ.≤-trans H>0 (ℕ.≤-reflexive (sym (ℕ.+-identityʳ H))))

  N≡H+H : N ≡ H ℕ+ H
  N≡H+H = cong (H ℕ+_) (ℕ.+-identityʳ H)

  N∣0 : (+ N) ∣ 0ℤ
  N∣0 = ∣ᵤ⇒∣ (ℕDiv.divides 0 refl)

  -- N does not divide a non-zero integer of magnitude below it.

  N∤ : ∀ (z : ℤ) (j : ℕ) → ∣ z ∣ ≡ j → 0 < j → j < N → ¬ ((+ N) ∣ z)
  N∤ z j eq 0<j j<N d with ∣⇒∣ᵤ d
  ... | ℕDiv.divides zero    e = contradiction (trans (sym eq) e) (ℕ.>⇒≢ 0<j)
  ... | ℕDiv.divides (suc q) e = contradiction
        (ℕ.≤-trans (ℕ.m≤m+n N (q ℕ* N))
                   (ℕ.≤-reflexive (trans (sym e) eq)))
        (ℕ.<⇒≱ j<N)

coeff-zpow0-0 : coeff (zpow 0ℤ) (+ 0) ≡ 1ℤ
coeff-zpow0-0 = trans (coeff-zpow 0ℤ (+ 0)) (χ-1 N∣0)

coeff-zpow0-off : ∀ j → 0 < j → j < H → coeff (zpow 0ℤ) (+ j) ≡ 0ℤ
coeff-zpow0-off j 0<j j<H = trans (coeff-zpow 0ℤ (+ j))
  (χ-0 (N∤ (0ℤ - (+ j)) j abs₁ 0<j (ℕ.<-trans j<H H<N))
       (N∤ ((0ℤ - (+ j)) - (+ H)) (j ℕ+ H) abs₂
           (ℕ.<-≤-trans 0<j (ℕ.m≤m+n j H)) j+H<N))
  where
  fold : ∀ x y → (0ℤ - x) - y ≡ - (x + y)
  fold = solve 2 (λ x y → (con 0ℤ :- x) :- y := :- (x :+ y)) refl

  abs₁ : ∣ 0ℤ - (+ j) ∣ ≡ j
  abs₁ = trans (cong ∣_∣ (+-identityˡ (- (+ j)))) (∣-i∣≡∣i∣ (+ j))

  abs₂ : ∣ (0ℤ - (+ j)) - (+ H) ∣ ≡ j ℕ+ H
  abs₂ = trans (cong ∣_∣ (fold (+ j) (+ H))) (∣-i∣≡∣i∣ (+ (j ℕ+ H)))

  j+H<N : j ℕ+ H < N
  j+H<N = subst (j ℕ+ H <_) (sym N≡H+H) (ℕ.+-monoˡ-< H j<H)

-- A sum whose terms vanish away from 0 is its term at 0.

Σ<-single : ∀ k (f : ℕ → ℤ) → 0 < k →
            (∀ j → 0 < j → j < k → f j ≡ 0ℤ) → Σ< k f ≡ f 0
Σ<-single zero    f () z
Σ<-single (suc k) f _ z = trans (Σ<-front k f)
  (trans (cong (λ x → f 0 + x)
               (Σ<-0 k (λ j j<k → z (suc j) (s≤s z≤n) (s≤s j<k))))
         (+-identityʳ (f 0)))

‖zpow0‖² : ‖ zpow 0ℤ ‖² ≡ 1ℤ
‖zpow0‖² = trans
  (Σ<-single H (λ j → coeff (zpow 0ℤ) (+ j) * coeff (zpow 0ℤ) (+ j)) H>0
    (λ j 0<j j<H → cong₂ _*_ (coeff-zpow0-off j 0<j j<H)
                             (coeff-zpow0-off j 0<j j<H)))
  (cong₂ _*_ coeff-zpow0-0 coeff-zpow0-0)
