------------------------------------------------------------------------
-- Presentations of groups
--
-- Maps on Z[ζ] that commute with the matrices of circuits
--
-- The gates of PathSum.CircuitSemantics build each entry of a new
-- column out of entries of the old one with two operations only: sums,
-- and rotations by powers of ζ.  So a map f on amplitudes that
-- respects equality, is additive and commutes with every rotation
-- commutes with every gate and every circuit, applied entry by entry
-- (PathSum.Miter's applyᴬ-linear).  Such a map is a Linear f here.
-- The instances are the identity, composites, pointwise sums,
-- rotations, multiplication by √2 and its powers, and multiplication
-- by an integer -- enough for the normalisations 1/√2^k and 2^k that
-- inverting a circuit produces.  Multiplication by any element of Z[ζ]
-- is linear too, but Z[ζ]'s product is not defined here.
--
-- The second half is bookkeeping of normalisations: powers of √2
-- compose by adding exponents and commute, and √2^j · √2^j = 2^j.
-- scale-+ and scale-exp are copies of PathSum.Denotation's private
-- lemmas of the same names.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.AmpLinear (M₀ : ℕ) where

open import Data.Integer.Base using (+_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-comm; *-assoc; *-comm; *-identityˡ; *-distribˡ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; _+ᴬ_; _·ᴬ_; rot; rot-map; rot-exp; rot-comp; rot-+ᴬ;
   rot-·ᴬ; √2·; √2·-map; √2·-twice; scale; scale-√2; c)
open import PathSum.Order (suc (suc (suc M₀))) using (pow; pow-suc; pow-+)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:=_)


------------------------------------------------------------------------
-- Linear maps

-- The field names say what the map is compared with; they avoid
-- Cyclotomic's own rot and _+ᴬ_.

record Linear (f : Amp → Amp) : Set where
  field
    map-≐   : ∀ {a b} → a ≐ b → f a ≐ f b
    map-+ᴬ  : ∀ a b → f (a +ᴬ b) ≐ (f a +ᴬ f b)
    map-rot : ∀ e a → f (rot e a) ≐ rot e (f a)

open Linear


------------------------------------------------------------------------
-- Instances

-- Linear maps include the identity, and are closed under composition
-- and pointwise sums.

id-linear : Linear (λ a → a)
id-linear .map-≐   ab      = ab
id-linear .map-+ᴬ  a b _   = refl
id-linear .map-rot e a _   = refl

∘-linear : ∀ {f g} → Linear f → Linear g → Linear (λ a → f (g a))
∘-linear {f} {g} F G .map-≐ ab = map-≐ F (map-≐ G ab)
∘-linear {f} {g} F G .map-+ᴬ a b i =
  trans (map-≐ F (map-+ᴬ G a b) i) (map-+ᴬ F (g a) (g b) i)
∘-linear {f} {g} F G .map-rot e a i =
  trans (map-≐ F (map-rot G e a) i) (map-rot F e (g a) i)

+-linear : ∀ {f g} → Linear f → Linear g → Linear (λ a → f a +ᴬ g a)
+-linear {f} {g} F G .map-≐ ab i =
  cong₂ _+_ (map-≐ F ab i) (map-≐ G ab i)
+-linear {f} {g} F G .map-+ᴬ a b i =
  trans (cong₂ _+_ (map-+ᴬ F a b i) (map-+ᴬ G a b i))
        (shuffle (f a i) (f b i) (g a i) (g b i))
  where
  shuffle : ∀ p q r s → (p + q) + (r + s) ≡ (p + r) + (q + s)
  shuffle = solve 4 (λ p q r s →
    (p :+ q) :+ (r :+ s) := (p :+ r) :+ (q :+ s)) refl
+-linear {f} {g} F G .map-rot e a i =
  trans (cong₂ _+_ (map-rot F e a i) (map-rot G e a i))
        (sym (rot-+ᴬ e (f a) (g a) i))

-- A rotation commutes with rotations: the two composites are rotations
-- by e + e′ and e′ + e, which rot-exp identifies.

rot-linear : ∀ e → Linear (rot e)
rot-linear e .map-≐   ab = rot-map e ab
rot-linear e .map-+ᴬ  a b = rot-+ᴬ e a b
rot-linear e .map-rot e′ a i =
  trans (rot-comp e e′ a i)
    (trans (rot-exp {e + e′} {e′ + e} a (+-comm e e′) i)
           (sym (rot-comp e′ e a i)))

-- √2 = ζ^c + ζ^(-c), so multiplying by it, or by a power of it, is
-- linear.

√2·-linear : Linear √2·
√2·-linear = +-linear (rot-linear (+ c)) (rot-linear (- (+ c)))

scale-linear : ∀ j → Linear (scale j)
scale-linear zero    = id-linear
scale-linear (suc j) = ∘-linear √2·-linear (scale-linear j)

-- Multiplying by an integer.

·ᴬ-linear : ∀ z → Linear (λ a → z ·ᴬ a)
·ᴬ-linear z .map-≐   ab i  = cong (λ u → z * u) (ab i)
·ᴬ-linear z .map-+ᴬ  a b i = *-distribˡ-+ z (a i) (b i)
·ᴬ-linear z .map-rot e a i = sym (rot-·ᴬ e z a i)


------------------------------------------------------------------------
-- Powers of √2

-- Exponents add, and may be changed along an equation.

scale-+ : ∀ a b w → scale a (scale b w) ≐ scale (a ℕ+ b) w
scale-+ zero    b w _ = refl
scale-+ (suc a) b w   = √2·-map (scale-+ a b w)

scale-exp : ∀ {a b} w → a ≡ b → scale a w ≐ scale b w
scale-exp w refl _ = refl

scale-comm : ∀ a b w → scale a (scale b w) ≐ scale b (scale a w)
scale-comm a b w i =
  trans (scale-+ a b w i)
    (trans (scale-exp w (ℕ.+-comm a b) i) (sym (scale-+ b a w i)))

-- √2^j · √2^j = 2^j.

scale-twice : ∀ j w → scale j (scale j w) ≐ pow j ·ᴬ w
scale-twice zero    w i = sym (*-identityˡ (w i))
scale-twice (suc j) w i =
  trans (√2·-map (scale-√2 j (scale j w)) i)
    (trans (√2·-twice (scale j (scale j w)) i)
      (trans (cong (λ u → (+ 2) * u) (scale-twice j w i))
        (trans (sym (*-assoc (+ 2) (pow j) (w i)))
               (cong (λ u → u * w i)
                     (trans (*-comm (+ 2) (pow j)) (sym (pow-suc j)))))))

-- Powers of 2 multiply by adding exponents.

pow-·ᴬ : ∀ a b w → pow a ·ᴬ (pow b ·ᴬ w) ≐ pow (a ℕ+ b) ·ᴬ w
pow-·ᴬ a b w i =
  trans (sym (*-assoc (pow a) (pow b) (w i)))
        (cong (λ u → u * w i) (pow-+ a b))
