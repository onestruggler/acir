------------------------------------------------------------------------
-- Presentations of groups
--
-- Signs in Z[ζ], and columns of integers
--
-- Every phase of the hidden shift algorithm is a half: a Hadamard
-- contributes ½ x·y, an oracle ½ f.  In Z[ζ] the power ζ^(½ v) of a
-- half is the sign (-1)^v, which depends only on the parity of the
-- integer v (zpow-½), since ½ is H and ζ^H = -1.  The parity is
-- PathSum.Polynomial.Bind's odd -- the same test PathSum.Denotation
-- applies to an output -- and it is additive (odd-+), which is what
-- turns the value of a sum of monomials into an exclusive or.
--
-- A column all of whose entries are integer multiples of ζ^0, ⌈ c ⌉,
-- is then an integer vector in disguise: rotating an entry by ζ^(½ v)
-- multiplies it by (-1)^v (rot-½), and a sum of such entries is the
-- integer sum PathSum.AssignSum.Σᶻ of their coefficients (Σᴮ-ᶻ).  The
-- whole of the algorithm runs on columns of this form, so that its
-- interference is computed over the integers (PathSum.HiddenShift.
-- Walsh) rather than in Z[ζ].
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Sign (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣m+n∣m⇒∣n; ∣⇒∣ᵤ)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ;
   *-distribʳ-+; -1*i≡-i; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.AssignSum using
  (Σᶻ; Σᶻ-zero; Σᶻ-suc; Σᶻ-cong; RespectsZ; _∷ᵃ_)
open import PathSum.CircuitSemantics M₀ using (Column)
open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; _·ᴬ_; _≐_; H; N; extend; Σᴮ; zpow; zpow-anti; zpow-cong; rot;
   rot-·ᴬ; rot-zpow)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Order 0 using (parity)
open import PathSum.Polynomial using (sgn)
open import PathSum.Polynomial.Bind using (odd)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Reduction M using (½)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- Parities

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  odd-even : ∀ {z} → (+ 2) ∣ z → odd z ≡ false
  odd-even {z} d with (+ 2) ∣? z
  ... | yes _  = refl
  ... | no ¬d = contradiction d ¬d

  odd-odd : ∀ {z} → ¬ ((+ 2) ∣ z) → odd z ≡ true
  odd-odd {z} ¬d with (+ 2) ∣? z
  ... | yes d = contradiction d ¬d
  ... | no _  = refl

-- The parity of r·2 + b is b.

odd-rep : ∀ r b → odd (r * (+ 2) + [ b ]ᶻ) ≡ b
odd-rep r false = odd-even (divides r (+-identityʳ (r * (+ 2))))
odd-rep r true  = odd-odd (λ d → 2∤1 (∣m+n∣m⇒∣n d (divides r refl)))

odd-[] : ∀ b → odd [ b ]ᶻ ≡ b
odd-[] b = trans (cong odd (sym (+-identityˡ [ b ]ᶻ))) (odd-rep 0ℤ b)

-- Every integer is twice something plus its parity.

halve : ∀ a → Σ ℤ (λ r → a ≡ r * (+ 2) + [ odd a ]ᶻ)
halve a with parity a
... | inj₁ (r , eq) = r , trans eq (sym (trans
        (cong (λ b → r * (+ 2) + [ b ]ᶻ) (odd-even (divides r eq)))
        (+-identityʳ (r * (+ 2)))))
... | inj₂ (r , eq) = r , trans eq
        (cong (λ b → r * (+ 2) + [ b ]ᶻ)
              (sym (odd-odd (λ d → 2∤1 (∣m+n∣m⇒∣n (subst ((+ 2) ∣_) eq d)
                                                   (divides r refl))))))

-- Parity is additive.

odd-+ : ∀ a b → odd (a + b) ≡ odd a xor odd b
odd-+ a b with halve a | halve b
... | ra , ea | rb , eb =
  trans (cong odd whole) (odd-rep (ra + rb + [ p ∧ q ]ᶻ) (p xor q))
  where
  p q : Bool
  p = odd a
  q = odd b

  carry : ∀ s t → [ s ]ᶻ + [ t ]ᶻ ≡ [ s ∧ t ]ᶻ * (+ 2) + [ s xor t ]ᶻ
  carry false false = refl
  carry false true  = refl
  carry true  false = refl
  carry true  true  = refl

  gather : ∀ u v t → (u * (+ 2) + t) + (v * (+ 2)) ≡ (u + v) * (+ 2) + t
  gather = solve 3 (λ u v t → (u :* con (+ 2) :+ t) :+ (v :* con (+ 2))
                              := (u :+ v) :* con (+ 2) :+ t) refl

  regroup : ∀ u v s t →
            (u * (+ 2) + s) + (v * (+ 2) + t) ≡ ((u + v) * (+ 2)) + (s + t)
  regroup = solve 4 (λ u v s t →
    (u :* con (+ 2) :+ s) :+ (v :* con (+ 2) :+ t) :=
    ((u :+ v) :* con (+ 2)) :+ (s :+ t)) refl

  whole : a + b ≡ (ra + rb + [ p ∧ q ]ᶻ) * (+ 2) + [ p xor q ]ᶻ
  whole = trans (cong₂ _+_ ea eb)
    (trans (regroup ra rb [ p ]ᶻ [ q ]ᶻ)
      (trans (cong (λ t → (ra + rb) * (+ 2) + t) (carry p q))
        (sym (trans (cong (_+ [ p xor q ]ᶻ)
                          (*-distribʳ-+ (+ 2) (ra + rb) [ p ∧ q ]ᶻ))
                    (solve 3 (λ u w t → (u :+ w) :+ t := u :+ (w :+ t)) refl
                             ((ra + rb) * (+ 2)) ([ p ∧ q ]ᶻ * (+ 2))
                             [ p xor q ]ᶻ)))))

-- The parity of a product of bits is their conjunction.

odd-∧ : ∀ a b → odd ([ a ]ᶻ * [ b ]ᶻ) ≡ a ∧ b
odd-∧ false false = odd-[] false
odd-∧ false true  = odd-[] false
odd-∧ true  false = odd-[] false
odd-∧ true  true  = odd-[] true


------------------------------------------------------------------------
-- Halves of a turn

-- The unit ζ^0.

1ᴬ : Amp
1ᴬ = zpow 0ℤ

-- ζ^(½ b) is (-1)^b: ½ is H, and ζ^H = -1.

zpow-½-bit : ∀ b → zpow (½ * [ b ]ᶻ) ≐ sgn b ·ᴬ 1ᴬ
zpow-½-bit false i =
  trans (zpow-≡ (*-zeroʳ ½) i) (sym (*-identityˡ (zpow 0ℤ i)))
zpow-½-bit true  i = trans (zpow-≡ (*-identityʳ ½) i)
  (trans (zpow-anti 0ℤ i) (sym (-1*i≡-i (zpow 0ℤ i))))

-- Two integers of the same parity differ by an even number.

odd-≡ : ∀ a b → odd a ≡ odd b → (+ 2) ∣ (a - b)
odd-≡ a b eq with halve a | halve b
... | ra , ea | rb , eb = divides (ra - rb) (trans
  (cong₂ _-_ ea (trans eb (cong (λ t → rb * (+ 2) + [ t ]ᶻ) (sym eq))))
  (shape ra rb [ odd a ]ᶻ))
  where
  shape : ∀ u v t → (u * (+ 2) + t) - (v * (+ 2) + t) ≡ (u - v) * (+ 2)
  shape = solve 3 (λ u v t → (u :* con (+ 2) :+ t) :- (v :* con (+ 2) :+ t)
                             := (u :- v) :* con (+ 2)) refl

-- Half of an integer is half of its parity, modulo N: ½ · 2 is N, the
-- order of ζ.

½-parity : ∀ v → (+ N) ∣ (½ * v - ½ * [ odd v ]ᶻ)
½-parity v with halve v
... | r , eq = divides r (trans (cong (λ w → ½ * w - ½ * [ odd v ]ᶻ) eq)
  (trans (shape ½ r [ odd v ]ᶻ) (cong (r *_) ½·2)))
  where
  ½·2 : ½ * (+ 2) ≡ + N
  ½·2 = trans (sym (pos-* H 2)) (cong +_ (ℕ.*-comm H 2))

  shape : ∀ h u t → h * (u * (+ 2) + t) - h * t ≡ u * (h * (+ 2))
  shape = solve 3 (λ h u t → h :* (u :* con (+ 2) :+ t) :- h :* t
                             := u :* (h :* con (+ 2))) refl

-- So ζ^(½ v) depends only on the parity of v.

zpow-½ : ∀ v → zpow (½ * v) ≐ sgn (odd v) ·ᴬ 1ᴬ
zpow-½ v i = trans (zpow-cong {½ * v} {½ * [ odd v ]ᶻ} (½-parity v) i)
                   (zpow-½-bit (odd v) i)

-- Rotating an integer multiple of ζ^0 by ζ^(½ v) multiplies it by
-- (-1)^v.

rot-½ : ∀ v (c : ℤ) → rot (½ * v) (c ·ᴬ 1ᴬ) ≐ (sgn (odd v) * c) ·ᴬ 1ᴬ
rot-½ v c i = trans (rot-·ᴬ (½ * v) c 1ᴬ i)
  (trans (cong (c *_) (trans (rot-zpow (½ * v) 0ℤ i)
                        (trans (zpow-≡ (+-identityʳ (½ * v)) i)
                               (zpow-½ v i))))
         (shape c (sgn (odd v)) (zpow 0ℤ i)))
  where
  shape : ∀ u s t → u * (s * t) ≡ (s * u) * t
  shape = solve 3 (λ u s t → u :* (s :* t) := (s :* u) :* t) refl


------------------------------------------------------------------------
-- Columns of integers

-- The column whose entry at w is the integer c w, as a multiple of
-- ζ^0.

⌈_⌉ : (Assign n → ℤ) → Column n
⌈ c ⌉ w = c w ·ᴬ 1ᴬ

-- A sum of integer multiples of one amplitude is the integer sum of
-- the multiples.  Σᴮ visits true first and Σᶻ false first, and their
-- assignments are built by different constructors, so the summand
-- must read its assignment only through its values.

Σᴮ-ᶻ : (a : Assign k → ℤ) → RespectsZ a → (u : Amp) →
       Σᴮ (λ w → a w ·ᴬ u) ≐ Σᶻ a ·ᴬ u
Σᴮ-ᶻ {zero}  a resp u i = cong (_* u i) (sym (Σᶻ-zero a))
Σᴮ-ᶻ {suc k} a resp u i = trans
  (cong₂ _+_ (Σᴮ-ᶻ (λ g → a (extend true g))  (half true)  u i)
             (Σᴮ-ᶻ (λ g → a (extend false g)) (half false) u i))
  (trans (cong₂ (λ s t → s * u i + t * u i) (same true) (same false))
    (trans (+-comm (Σᶻ (λ g → a (true ∷ᵃ g)) * u i)
                   (Σᶻ (λ g → a (false ∷ᵃ g)) * u i))
      (trans (sym (*-distribʳ-+ (u i) (Σᶻ (λ g → a (false ∷ᵃ g)))
                                      (Σᶻ (λ g → a (true ∷ᵃ g)))))
             (cong (_* u i) (sym (Σᶻ-suc a))))))
  where
  pt : ∀ b (g : Assign k) j → extend b g j ≡ (b ∷ᵃ g) j
  pt b g zero    = refl
  pt b g (suc j) = refl

  ext-cong : ∀ b {g h : Assign k} → (∀ j → g j ≡ h j) →
             ∀ j → extend b g j ≡ extend b h j
  ext-cong b g≗h zero    = refl
  ext-cong b g≗h (suc j) = g≗h j

  half : ∀ b → RespectsZ (λ g → a (extend b g))
  half b g h g≗h = resp (extend b g) (extend b h) (ext-cong b g≗h)

  same : ∀ b → Σᶻ (λ g → a (extend b g)) ≡ Σᶻ (λ g → a (b ∷ᵃ g))
  same b = Σᶻ-cong (λ g → resp (extend b g) (b ∷ᵃ g) (pt b g))
