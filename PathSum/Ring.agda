------------------------------------------------------------------------
-- Presentations of groups
--
-- Multiplication and conjugation in Z[ζ]
--
-- PathSum.Cyclotomic represents an element of Z[ζ] by its coordinates
-- a₀ … a_(H-1) in the basis ζ^0 … ζ^(H-1), and reads a coefficient at
-- any integer exponent through `coeff`, the relation ζ^H = -1 turning
-- an exponent outside the window into a sign.  This module makes Z[ζ]
-- a ring with involution on that representation.
--
-- The product a ⊛ b is Σ_j a_j ζ^j · b, whose coefficient at i is the
-- negacyclic convolution Σ_{j<H} a_j · b_(i-j), the coefficient
-- b_(i-j) being read through `coeff` when i - j leaves the window.
-- Conjugation is ζ ↦ ζ⁻¹, the automorphism that complex conjugation
-- induces on Z[ζ]: the coefficient of conj a at i is that of a at -i.
-- Both are defined on coordinates, and both are shown to act on the
-- coefficient at every exponent the same way (coeff-⊛, coeff-conj),
-- which is what lets proofs work with `coeff` throughout.
--
-- Proofs about ⊛ come down to moving the window of summation.  The
-- summands involved -- a_t b_(u-t) for a product, a_t b_(t+u) for a
-- product with a conjugate -- are H-periodic in t, both factors
-- changing sign under a shift by H, and PathSum.Norm's Window lemma
-- moves the window of an H-periodic summand anywhere.  That gives
-- ζ^e ⊛ b = ζ^e · b, the unit, rotations on either side, and the
-- Hermitian symmetry conj (a ⊛ conj b) = b ⊛ conj a.
--
-- The identity connecting the ring to lemma 4.1 is that the constant
-- coefficient of a ⊛ conj b is the trace form ⟪ a , b ⟫ of
-- PathSum.Norm.  So ‖ a ‖², which PathSum.Norm introduces as Σ_i a_i²,
-- is the constant coefficient of a·ā -- that is, Tr(a·ā)/H -- as a
-- theorem, and a₀² ≤ ‖ a ‖² bounds the constant coefficient itself.
--
-- The laws proved are the ones the Hermitian product of columns
-- (PathSum.Hermitian) and definition 2.4 (PathSum.PartialIsometry)
-- use: congruence, bilinearity, zero and a left unit, powers of ζ, the
-- conjugation laws, the Hermitian identities above, and that √2 passes
-- through a product, so that √2·a · conj (√2·b) = 2 · a·b̄ (which is
-- what lets definition 2.4 be stated with the normalisation cleared).
-- Commutativity and associativity of ⊛, and conj being multiplicative,
-- are not proved: those two modules do not need them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ring (M₀ : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Integer.Base using
  (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_; _≤_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣-refl; ∣m⇒∣-m; ∣m∣n⇒∣m-n)
open import Data.Integer.Properties using
  (+-comm; +-identityʳ; +-inverseʳ; neg-involutive; neg-distribʳ-*;
   *-distribˡ-+; *-distribʳ-+; *-comm; *-assoc; *-zeroˡ; *-zeroʳ;
   *-identityˡ; pos-+; +-monoʳ-≤; ≤-trans; ≤-reflexive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _<_) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Cyclotomic M₀
open import PathSum.Norm M₀ using
  (Σ<; Σ<-cong; Σ<-+; Σ<-*; Σ<-neg; Σ<-0; Σ<-front; Σ<-≥0; Σ<-single;
   module Window; coeff-at⁺; coeff-at⁻; coeff-rot; coeff-neg; coeff-sub;
   coeff-0ᴬ; coeff-zpow0-0; coeff-zpow0-off; H>0; neg*neg; sq≥0;
   ⟪_,_⟫; ‖_‖²)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)


------------------------------------------------------------------------
-- Coefficients and sums

-- A coefficient read at two exponents known to be equal.  Exponents
-- are changed only through this lemma, with both written out: left to
-- conversion, a comparison of coefficients at syntactically different
-- exponents unfolds `classify`.

coeff-exp : ∀ a w w′ → w ≡ w′ → coeff a w ≡ coeff a w′
coeff-exp a w w′ refl = refl

-- ζ^(-H) = -1 as well.

coeff-anti⁻ : ∀ a w → coeff a (w - (+ H)) ≡ - coeff a w
coeff-anti⁻ a w =
  trans (sym (neg-involutive (coeff a (w - (+ H))))) (cong -_ (sym up))
  where
  back : ∀ u t → (u - t) + t ≡ u
  back = solve 2 (λ u t → (u :- t) :+ t := u) refl

  up : coeff a w ≡ - coeff a (w - (+ H))
  up = trans (coeff-exp a w ((w - (+ H)) + (+ H)) (sym (back w (+ H))))
             (coeff-anti a (w - (+ H)))

-- A sum of non-negative terms is at least its first term.

Σ<-head≤ : ∀ k (f : ℕ → ℤ) → 0 < k → (∀ j → 0ℤ ≤ f j) → f 0 ≤ Σ< k f
Σ<-head≤ zero    f ()  nn
Σ<-head≤ (suc k) f _   nn = ≤-trans
  (≤-trans (≤-reflexive (sym (+-identityʳ (f 0))))
           (+-monoʳ-≤ (f 0) (Σ<-≥0 k (λ j → f (suc j)) (λ j → nn (suc j)))))
  (≤-reflexive (sym (Σ<-front k f)))

private
  Σ<-sub : ∀ k (f g : ℕ → ℤ) → Σ< k (λ j → f j - g j) ≡ Σ< k f - Σ< k g
  Σ<-sub k f g =
    trans (Σ<-+ k f (λ j → - g j)) (cong (λ t → Σ< k f + t) (Σ<-neg k g))

  -- The summands of a product and of a product with a conjugate are
  -- H-periodic: both factors change sign under a shift by H.

  per-conv : ∀ a b u w →
             coeff a (w + (+ H)) * coeff b (u - (w + (+ H))) ≡
             coeff a w * coeff b (u - w)
  per-conv a b u w = trans
    (cong₂ _*_ (coeff-anti a w)
      (trans (coeff-exp b (u - (w + (+ H))) ((u - w) - (+ H))
                          (shape u w (+ H)))
             (coeff-anti⁻ b (u - w))))
    (neg*neg (coeff a w) (coeff b (u - w)))
    where
    shape : ∀ u w t → u - (w + t) ≡ (u - w) - t
    shape = solve 3 (λ u w t → u :- (w :+ t) := (u :- w) :- t) refl

  per-corr : ∀ a b u w →
             coeff a (w + (+ H)) * coeff b ((w + (+ H)) + u) ≡
             coeff a w * coeff b (w + u)
  per-corr a b u w = trans
    (cong₂ _*_ (coeff-anti a w)
      (trans (coeff-exp b ((w + (+ H)) + u) ((w + u) + (+ H))
                          (shape w (+ H) u))
             (coeff-anti b (w + u))))
    (neg*neg (coeff a w) (coeff b (w + u)))
    where
    shape : ∀ w t u → (w + t) + u ≡ (w + u) + t
    shape = solve 3 (λ w t u → (w :+ t) :+ u := (w :+ u) :+ t) refl


------------------------------------------------------------------------
-- The product

-- a ⊛ b = Σ_j a_j ζ^j · b: its coordinate at i is the negacyclic
-- convolution of the coordinates.

infixl 7 _⊛_

_⊛_ : Amp → Amp → Amp
(a ⊛ b) i = Σ< H (λ j → coeff a (+ j) * coeff b ((+ toℕ i) - (+ j)))

private
  -- The convolution read at an arbitrary exponent u.  Lemmas about a
  -- coordinate of a product are proved at a variable u and then used
  -- at u = + toℕ i, so that no exponent is ever rewritten in place.

  conv : Amp → Amp → ℤ → ℤ
  conv a b u = Σ< H (λ j → coeff a (+ j) * coeff b (u - (+ j)))

-- The convolution describes the coefficient of a product at every
-- exponent, not only inside the window.

coeff-⊛ : ∀ a b w →
          coeff (a ⊛ b) w ≡ Σ< H (λ j → coeff a (+ j) * coeff b (w - (+ j)))
coeff-⊛ a b w = go (classify w)
  where
  go : Class w →
       coeff (a ⊛ b) w ≡ Σ< H (λ j → coeff a (+ j) * coeff b (w - (+ j)))
  go (pos i d) = trans (coeff-at⁺ (a ⊛ b) w i d) (Σ<-cong H (λ j →
    cong (coeff a (+ j) *_)
      (sym (coeff-cong b (w - (+ j)) ((+ toℕ i) - (+ j))
             (subst ((+ N) ∣_) (shape w (+ toℕ i) (+ j)) d)))))
    where
    shape : ∀ u v x → u - v ≡ (u - x) - (v - x)
    shape = solve 3 (λ u v x → u :- v := (u :- x) :- (v :- x)) refl
  go (neg i d) = trans (coeff-at⁻ (a ⊛ b) w i d)
    (trans (sym (Σ<-neg H (λ j → coeff a (+ j) *
                                 coeff b ((+ toℕ i) - (+ j)))))
           (Σ<-cong H term))
    where
    shape : ∀ u v x t → u - (v + t) ≡ (u - x) - ((v - x) + t)
    shape = solve 4 (λ u v x t →
      u :- (v :+ t) := (u :- x) :- ((v :- x) :+ t)) refl

    term : ∀ j → - (coeff a (+ j) * coeff b ((+ toℕ i) - (+ j))) ≡
                 coeff a (+ j) * coeff b (w - (+ j))
    term j = trans (neg-distribʳ-* (coeff a (+ j))
                                   (coeff b ((+ toℕ i) - (+ j))))
      (cong (coeff a (+ j) *_) (sym (trans
        (coeff-cong b (w - (+ j)) (((+ toℕ i) - (+ j)) + (+ H))
          (subst ((+ N) ∣_) (shape w (+ toℕ i) (+ j) (+ H)) d))
        (coeff-anti b ((+ toℕ i) - (+ j))))))

-- Congruence and bilinearity, coefficient by coefficient.

⊛-cong : ∀ {a a′ b b′} → a ≐ a′ → b ≐ b′ → a ⊛ b ≐ a′ ⊛ b′
⊛-cong {a} {a′} {b} {b′} a≐a′ b≐b′ i = go (+ toℕ i)
  where
  go : ∀ u → conv a b u ≡ conv a′ b′ u
  go u = Σ<-cong H (λ j →
    cong₂ _*_ (coeff-map a≐a′ (+ j)) (coeff-map b≐b′ (u - (+ j))))

⊛-distribˡ-+ᴬ : ∀ a b c → a ⊛ (b +ᴬ c) ≐ a ⊛ b +ᴬ a ⊛ c
⊛-distribˡ-+ᴬ a b c i = go (+ toℕ i)
  where
  go : ∀ u → conv a (b +ᴬ c) u ≡ conv a b u + conv a c u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (coeff a (+ j) *_) (coeff-+ b c (u - (+ j))))
            (*-distribˡ-+ (coeff a (+ j)) (coeff b (u - (+ j)))
                                          (coeff c (u - (+ j))))))
    (Σ<-+ H (λ j → coeff a (+ j) * coeff b (u - (+ j)))
            (λ j → coeff a (+ j) * coeff c (u - (+ j))))

⊛-distribʳ-+ᴬ : ∀ a b c → (a +ᴬ b) ⊛ c ≐ a ⊛ c +ᴬ b ⊛ c
⊛-distribʳ-+ᴬ a b c i = go (+ toℕ i)
  where
  go : ∀ u → conv (a +ᴬ b) c u ≡ conv a c u + conv b c u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (_* coeff c (u - (+ j))) (coeff-+ a b (+ j)))
            (*-distribʳ-+ (coeff c (u - (+ j))) (coeff a (+ j))
                                                (coeff b (+ j)))))
    (Σ<-+ H (λ j → coeff a (+ j) * coeff c (u - (+ j)))
            (λ j → coeff b (+ j) * coeff c (u - (+ j))))

⊛-distribˡ-diff : ∀ a b c → a ⊛ (b -ᴬ c) ≐ a ⊛ b -ᴬ a ⊛ c
⊛-distribˡ-diff a b c i = go (+ toℕ i)
  where
  law : ∀ x y z → x * (y - z) ≡ (x * y) - (x * z)
  law = solve 3 (λ x y z → x :* (y :- z) := (x :* y) :- (x :* z)) refl

  go : ∀ u → conv a (b -ᴬ c) u ≡ conv a b u - conv a c u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (coeff a (+ j) *_) (coeff-sub b c (u - (+ j))))
            (law (coeff a (+ j)) (coeff b (u - (+ j)))
                                 (coeff c (u - (+ j))))))
    (Σ<-sub H (λ j → coeff a (+ j) * coeff b (u - (+ j)))
              (λ j → coeff a (+ j) * coeff c (u - (+ j))))

⊛-distribʳ-diff : ∀ a b c → (a -ᴬ b) ⊛ c ≐ a ⊛ c -ᴬ b ⊛ c
⊛-distribʳ-diff a b c i = go (+ toℕ i)
  where
  law : ∀ x y z → (x - y) * z ≡ (x * z) - (y * z)
  law = solve 3 (λ x y z → (x :- y) :* z := (x :* z) :- (y :* z)) refl

  go : ∀ u → conv (a -ᴬ b) c u ≡ conv a c u - conv b c u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (_* coeff c (u - (+ j))) (coeff-sub a b (+ j)))
            (law (coeff a (+ j)) (coeff b (+ j)) (coeff c (u - (+ j))))))
    (Σ<-sub H (λ j → coeff a (+ j) * coeff c (u - (+ j)))
              (λ j → coeff b (+ j) * coeff c (u - (+ j))))

⊛-·ᴬˡ : ∀ (z : ℤ) a b → (z ·ᴬ a) ⊛ b ≐ z ·ᴬ (a ⊛ b)
⊛-·ᴬˡ z a b i = go (+ toℕ i)
  where
  go : ∀ u → conv (z ·ᴬ a) b u ≡ z * conv a b u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (_* coeff b (u - (+ j))) (coeff-·ᴬ z a (+ j)))
            (*-assoc z (coeff a (+ j)) (coeff b (u - (+ j))))))
    (Σ<-* H z (λ j → coeff a (+ j) * coeff b (u - (+ j))))

⊛-·ᴬʳ : ∀ (z : ℤ) a b → a ⊛ (z ·ᴬ b) ≐ z ·ᴬ (a ⊛ b)
⊛-·ᴬʳ z a b i = go (+ toℕ i)
  where
  swap : ∀ x y w → x * (y * w) ≡ y * (x * w)
  swap = solve 3 (λ x y w → x :* (y :* w) := y :* (x :* w)) refl

  go : ∀ u → conv a (z ·ᴬ b) u ≡ z * conv a b u
  go u = trans
    (Σ<-cong H (λ j →
      trans (cong (coeff a (+ j) *_) (coeff-·ᴬ z b (u - (+ j))))
            (swap (coeff a (+ j)) z (coeff b (u - (+ j))))))
    (Σ<-* H z (λ j → coeff a (+ j) * coeff b (u - (+ j))))

·ᴬ-cong : ∀ (z : ℤ) {a b} → a ≐ b → z ·ᴬ a ≐ z ·ᴬ b
·ᴬ-cong z a≐b i = cong (z *_) (a≐b i)

·ᴬ-·ᴬ : ∀ (y z : ℤ) a → y ·ᴬ (z ·ᴬ a) ≐ (y * z) ·ᴬ a
·ᴬ-·ᴬ y z a i = sym (*-assoc y z (a i))

⊛-zeroˡ : ∀ b → 0ᴬ ⊛ b ≐ 0ᴬ
⊛-zeroˡ b i = go (+ toℕ i)
  where
  go : ∀ u → conv 0ᴬ b u ≡ 0ℤ
  go u = Σ<-0 H (λ j _ →
    trans (cong (_* coeff b (u - (+ j))) (coeff-0ᴬ (+ j)))
          (*-zeroˡ (coeff b (u - (+ j)))))

⊛-zeroʳ : ∀ a → a ⊛ 0ᴬ ≐ 0ᴬ
⊛-zeroʳ a i = go (+ toℕ i)
  where
  go : ∀ u → conv a 0ᴬ u ≡ 0ℤ
  go u = Σ<-0 H (λ j _ →
    trans (cong (coeff a (+ j) *_) (coeff-0ᴬ (u - (+ j))))
          (*-zeroʳ (coeff a (+ j))))


------------------------------------------------------------------------
-- Powers of ζ

-- ζ^0 is the unit: in the convolution with ζ^0 only the term j = 0
-- survives, since ζ^0 has no other coefficient in the window.

private
  unit-sum : ∀ w b → conv (zpow 0ℤ) b w ≡ coeff b w
  unit-sum w b = trans
    (Σ<-single H (λ j → coeff (zpow 0ℤ) (+ j) * coeff b (w - (+ j))) H>0
      (λ j 0<j j<H →
        trans (cong (_* coeff b (w - (+ j))) (coeff-zpow0-off j 0<j j<H))
              (*-zeroˡ (coeff b (w - (+ j))))))
    (trans (cong₂ _*_ coeff-zpow0-0
                      (coeff-exp b (w - (+ 0)) w (+-identityʳ w)))
           (*-identityˡ (coeff b w)))

⊛-identityˡ : ∀ b → zpow 0ℤ ⊛ b ≐ b
⊛-identityˡ b i = trans (unit-sum (+ toℕ i) b) (coeff-δ b i)

-- Multiplying by ζ^e is rotating by e.  Shifting the window by e
-- turns the coefficients of ζ^e into those of ζ^0.

zpow-⊛ : ∀ e b → zpow e ⊛ b ≐ rot e b
zpow-⊛ e b i = go (+ toℕ i)
  where
  shape₁ : ∀ e x → e - (x + e) ≡ 0ℤ - x
  shape₁ = solve 2 (λ e x → e :- (x :+ e) := con 0ℤ :- x) refl

  shape₂ : ∀ u e x → u - (x + e) ≡ (u - e) - x
  shape₂ = solve 3 (λ u e x → u :- (x :+ e) := (u :- e) :- x) refl

  go : ∀ u → conv (zpow e) b u ≡ coeff b (u - e)
  go u = trans (Σ<-cong H (λ j → cong g (sym (+-identityʳ (+ j)))))
    (trans (sym (Window.window g (per-conv (zpow e) b u) e))
      (trans (Σ<-cong H term) (unit-sum (u - e) b)))
    where
    g : ℤ → ℤ
    g t = coeff (zpow e) t * coeff b (u - t)

    term : ∀ j → g ((+ j) + e) ≡
                 coeff (zpow 0ℤ) (+ j) * coeff b ((u - e) - (+ j))
    term j = cong₂ _*_
      (trans (coeff-zpow e ((+ j) + e))
        (trans (cong χ (shape₁ e (+ j))) (sym (coeff-zpow 0ℤ (+ j)))))
      (coeff-exp b (u - ((+ j) + e)) ((u - e) - (+ j)) (shape₂ u e (+ j)))

zpow-⊛-zpow : ∀ e e′ → zpow e ⊛ zpow e′ ≐ zpow (e + e′)
zpow-⊛-zpow e e′ i = trans (zpow-⊛ e (zpow e′) i) (rot-zpow e e′ i)

-- A rotation of either factor is a rotation of the product.

⊛-rotʳ : ∀ e a b → a ⊛ rot e b ≐ rot e (a ⊛ b)
⊛-rotʳ e a b i = go (+ toℕ i)
  where
  shape : ∀ u x e → (u - x) - e ≡ (u - e) - x
  shape = solve 3 (λ u x e → (u :- x) :- e := (u :- e) :- x) refl

  go : ∀ u → conv a (rot e b) u ≡ coeff (a ⊛ b) (u - e)
  go u = trans
    (Σ<-cong H (λ j → cong (coeff a (+ j) *_)
      (trans (coeff-rot e b (u - (+ j)))
             (coeff-exp b ((u - (+ j)) - e) ((u - e) - (+ j))
                          (shape u (+ j) e)))))
    (sym (coeff-⊛ a b (u - e)))

⊛-rotˡ : ∀ e a b → rot e a ⊛ b ≐ rot e (a ⊛ b)
⊛-rotˡ e a b i = go (+ toℕ i)
  where
  shape : ∀ u e x → u - x ≡ (u - e) - (x - e)
  shape = solve 3 (λ u e x → u :- x := (u :- e) :- (x :- e)) refl

  go : ∀ u → conv (rot e a) b u ≡ coeff (a ⊛ b) (u - e)
  go u = trans (Σ<-cong H term)
    (trans (Window.rotate g (per-conv a b (u - e)) e)
           (sym (coeff-⊛ a b (u - e))))
    where
    g : ℤ → ℤ
    g t = coeff a t * coeff b ((u - e) - t)

    term : ∀ j → coeff (rot e a) (+ j) * coeff b (u - (+ j)) ≡
                 g ((+ j) - e)
    term j = cong₂ _*_ (coeff-rot e a (+ j))
      (coeff-exp b (u - (+ j)) ((u - e) - ((+ j) - e)) (shape u e (+ j)))


------------------------------------------------------------------------
-- Conjugation

-- ζ ↦ ζ⁻¹: the coefficient of conj a at i is that of a at -i.

conj : Amp → Amp
conj a i = coeff a (- (+ toℕ i))

-- ζ^(-z) and ζ^z have the same coefficient at 0: N divides -z exactly
-- when it divides z, and -z - H exactly when z - H, the two differing
-- from -(z - H) and z + H by N.  As in Cyclotomic's χ-anti, the
-- decisions are arguments, χ being mentioned at two exponents.

private
  N∣H+H : (+ N) ∣ ((+ H) + (+ H))
  N∣H+H = subst ((+ N) ∣_) (trans (cong +_ N≡H+H) (pos-+ H H)) ∣-refl
    where
    N≡H+H : N ≡ H ℕ+ H
    N≡H+H = cong (H ℕ+_) (ℕ.+-identityʳ H)

  ¬∣-neg : ∀ z → ¬ ((+ N) ∣ z) → ¬ ((+ N) ∣ (- z))
  ¬∣-neg z ¬d d = ¬d (subst ((+ N) ∣_) (neg-involutive z) (∣m⇒∣-m d))

  flip-H : ∀ z → (+ N) ∣ (z - (+ H)) → (+ N) ∣ ((- z) - (+ H))
  flip-H z d = subst ((+ N) ∣_) (shape z (+ H))
                     (∣m∣n⇒∣m-n (∣m⇒∣-m d) N∣H+H)
    where
    shape : ∀ z h → (- (z - h)) - (h + h) ≡ (- z) - h
    shape = solve 2 (λ z h → (:- (z :- h)) :- (h :+ h) := (:- z) :- h) refl

  unflip-H : ∀ z → (+ N) ∣ ((- z) - (+ H)) → (+ N) ∣ (z - (+ H))
  unflip-H z d = subst ((+ N) ∣_) (shape z (+ H))
                       (∣m∣n⇒∣m-n (∣m⇒∣-m d) N∣H+H)
    where
    shape : ∀ z h → (- ((- z) - h)) - (h + h) ≡ z - h
    shape = solve 2 (λ z h → (:- ((:- z) :- h)) :- (h :+ h) := z :- h) refl

  χ-neg-aux : ∀ z → Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ H))) →
              χ (- z) ≡ χ z
  χ-neg-aux z (yes d) _ = trans (χ-1 (∣m⇒∣-m d)) (sym (χ-1 {z} d))
  χ-neg-aux z (no ¬d) (yes b) =
    trans (χ--1 (¬∣-neg z ¬d) (flip-H z b)) (sym (χ--1 {z} ¬d b))
  χ-neg-aux z (no ¬d) (no ¬b) =
    trans (χ-0 (¬∣-neg z ¬d) (λ b → ¬b (unflip-H z b)))
          (sym (χ-0 {z} ¬d ¬b))

χ-neg : ∀ z → χ (- z) ≡ χ z
χ-neg z = χ-neg-aux z ((+ N) ∣? z) ((+ N) ∣? (z - (+ H)))

-- Conjugation acts on the coefficient at every exponent.

coeff-conj : ∀ a w → coeff (conj a) w ≡ coeff a (- w)
coeff-conj a w = go (classify w)
  where
  go : Class w → coeff (conj a) w ≡ coeff a (- w)
  go (pos i d) = trans (coeff-at⁺ (conj a) w i d)
    (sym (coeff-cong a (- w) (- (+ toℕ i))
           (subst ((+ N) ∣_) (shape w (+ toℕ i)) (∣m⇒∣-m d))))
    where
    shape : ∀ w v → - (w - v) ≡ (- w) - (- v)
    shape = solve 2 (λ w v → :- (w :- v) := (:- w) :- (:- v)) refl
  go (neg i d) = trans (coeff-at⁻ (conj a) w i d)
    (sym (trans (coeff-cong a (- w) ((- (+ toℕ i)) - (+ H))
                  (subst ((+ N) ∣_) (shape w (+ toℕ i) (+ H)) (∣m⇒∣-m d)))
                (coeff-anti⁻ a (- (+ toℕ i)))))
    where
    shape : ∀ w v t → - (w - (v + t)) ≡ (- w) - ((- v) - t)
    shape = solve 3 (λ w v t →
      :- (w :- (v :+ t)) := (:- w) :- ((:- v) :- t)) refl

-- The conjugation laws, coefficient by coefficient.

conj-cong : ∀ {a b} → a ≐ b → conj a ≐ conj b
conj-cong a≐b i = coeff-map a≐b (- (+ toℕ i))

conj-involutive : ∀ a → conj (conj a) ≐ a
conj-involutive a i = trans (coeff-conj a (- (+ toℕ i)))
  (trans (coeff-exp a (- (- (+ toℕ i))) (+ toℕ i) (neg-involutive (+ toℕ i)))
         (coeff-δ a i))

conj-+ᴬ : ∀ a b → conj (a +ᴬ b) ≐ conj a +ᴬ conj b
conj-+ᴬ a b i = coeff-+ a b (- (+ toℕ i))

conj-diff : ∀ a b → conj (a -ᴬ b) ≐ conj a -ᴬ conj b
conj-diff a b i = coeff-sub a b (- (+ toℕ i))

conj-neg : ∀ a → conj (-ᴬ a) ≐ -ᴬ conj a
conj-neg a i = coeff-neg a (- (+ toℕ i))

conj-·ᴬ : ∀ (z : ℤ) a → conj (z ·ᴬ a) ≐ z ·ᴬ conj a
conj-·ᴬ z a i = coeff-·ᴬ z a (- (+ toℕ i))

conj-0ᴬ : conj 0ᴬ ≐ 0ᴬ
conj-0ᴬ i = coeff-0ᴬ (- (+ toℕ i))

conj-zpow : ∀ e → conj (zpow e) ≐ zpow (- e)
conj-zpow e i = trans (coeff-zpow e (- (+ toℕ i)))
  (trans (cong χ (shape e (+ toℕ i))) (χ-neg ((- e) - (+ toℕ i))))
  where
  shape : ∀ e u → e - (- u) ≡ - ((- e) - u)
  shape = solve 2 (λ e u → e :- (:- u) := :- ((:- e) :- u)) refl

conj-rot : ∀ e a → conj (rot e a) ≐ rot (- e) (conj a)
conj-rot e a i = trans (coeff-rot e a (- (+ toℕ i)))
  (trans (coeff-exp a ((- (+ toℕ i)) - e) (- ((+ toℕ i) - (- e)))
                      (shape (+ toℕ i) e))
         (sym (coeff-conj a ((+ toℕ i) - (- e)))))
  where
  shape : ∀ u e → (- u) - e ≡ - (u - (- e))
  shape = solve 2 (λ u e → (:- u) :- e := :- (u :- (:- e))) refl

-- √2 = ζ^c + ζ^(-c) is real: conjugation swaps its two terms.

conj-√2 : ∀ a → conj (√2· a) ≐ √2· (conj a)
conj-√2 a i = trans (conj-+ᴬ (rot (+ c) a) (rot (- (+ c)) a) i)
  (trans (cong₂ _+_ (conj-rot (+ c) a i) (conj-rot (- (+ c)) a i))
    (trans (cong (λ t → rot (- (+ c)) (conj a) i + t)
                 (rot-exp (conj a) (neg-involutive (+ c)) i))
           (+-comm (rot (- (+ c)) (conj a) i) (rot (+ c) (conj a) i))))


------------------------------------------------------------------------
-- The Hermitian form on entries

-- The constant coefficient of a · b̄ is the trace form: the term j of
-- the convolution at 0 pairs a_j with the coefficient of b̄ at -j,
-- which is b_j.

⊛-conj-coeff0 : ∀ a b → coeff (a ⊛ conj b) 0ℤ ≡ ⟪ a , b ⟫
⊛-conj-coeff0 a b = trans (coeff-⊛ a (conj b) 0ℤ) (Σ<-cong H (λ j →
  cong (coeff a (+ j) *_)
    (trans (coeff-conj b (0ℤ - (+ j)))
           (coeff-exp b (- (0ℤ - (+ j))) (+ j) (shape (+ j))))))
  where
  shape : ∀ x → - (0ℤ - x) ≡ x
  shape = solve 1 (λ x → :- (con 0ℤ :- x) := x) refl

‖‖²-coeff0 : ∀ a → coeff (a ⊛ conj a) 0ℤ ≡ ‖ a ‖²
‖‖²-coeff0 a = ⊛-conj-coeff0 a a

-- The squared constant coefficient is one of the terms of the norm.

coeff0²≤‖‖² : ∀ a → coeff a 0ℤ * coeff a 0ℤ ≤ ‖ a ‖²
coeff0²≤‖‖² a = ≤-trans (≤-reflexive (cong₂ _*_ at0 at0))
  (Σ<-head≤ H (λ j → coeff a (+ j) * coeff a (+ j)) H>0
            (λ j → sq≥0 (coeff a (+ j))))
  where
  at0 : coeff a 0ℤ ≡ coeff a (+ 0)
  at0 = coeff-exp a 0ℤ (+ 0) refl

-- A common phase cancels from a · b̄: the rotation of a by e and that
-- of b̄ by -e combine to the rotation by 0.

⊛-conj-rot : ∀ e a b → rot e a ⊛ conj (rot e b) ≐ a ⊛ conj b
⊛-conj-rot e a b i =
  trans (⊛-cong {a = rot e a} {a′ = rot e a} (λ _ → refl) (conj-rot e b) i)
    (trans (⊛-rotˡ e a (rot (- e) (conj b)) i)
      (trans (rot-map e (⊛-rotʳ (- e) a (conj b)) i)
        (trans (rot-comp e (- e) (a ⊛ conj b) i)
          (trans (rot-exp (a ⊛ conj b) (+-inverseʳ e) i)
                 (rot-0 (a ⊛ conj b) i)))))

-- Hermitian symmetry: the conjugate of a · b̄ is b · ā.  Read at -i,
-- the convolution pairs a_j with b_(j+i); moving the window by i
-- pairs a_(j-i) with b_j, which is the convolution of b with ā at i.

⊛-conj-herm : ∀ a b → conj (a ⊛ conj b) ≐ b ⊛ conj a
⊛-conj-herm a b i = go (+ toℕ i)
  where
  shape₁ : ∀ u x → - ((- u) - x) ≡ x + u
  shape₁ = solve 2 (λ u x → :- ((:- u) :- x) := x :+ u) refl

  shape₂ : ∀ u x → x - u ≡ - (u - x)
  shape₂ = solve 2 (λ u x → x :- u := :- (u :- x)) refl

  shape₃ : ∀ u x → (x - u) + u ≡ x
  shape₃ = solve 2 (λ u x → (x :- u) :+ u := x) refl

  go : ∀ u → coeff (a ⊛ conj b) (- u) ≡ conv b (conj a) u
  go u = trans (coeff-⊛ a (conj b) (- u))
    (trans (Σ<-cong H left)
      (trans (sym (Window.rotate g (per-corr a b u) u))
             (Σ<-cong H right)))
    where
    g : ℤ → ℤ
    g t = coeff a t * coeff b (t + u)

    left : ∀ j → coeff a (+ j) * coeff (conj b) ((- u) - (+ j)) ≡ g (+ j)
    left j = cong (coeff a (+ j) *_)
      (trans (coeff-conj b ((- u) - (+ j)))
             (coeff-exp b (- ((- u) - (+ j))) ((+ j) + u) (shape₁ u (+ j))))

    right : ∀ j → g ((+ j) - u) ≡ coeff b (+ j) * coeff (conj a) (u - (+ j))
    right j = trans
      (cong₂ _*_ (coeff-exp a ((+ j) - u) (- (u - (+ j))) (shape₂ u (+ j)))
                 (coeff-exp b (((+ j) - u) + u) (+ j) (shape₃ u (+ j))))
      (trans (*-comm (coeff a (- (u - (+ j)))) (coeff b (+ j)))
             (cong (coeff b (+ j) *_) (sym (coeff-conj a (u - (+ j))))))

-- The parallelogram law for a · c̄, polarised: what a Hadamard needs,
-- at the level of amplitudes rather than of norms.

⊛-conj-parallelogram : ∀ a b c d →
  (a +ᴬ b) ⊛ conj (c +ᴬ d) +ᴬ (a -ᴬ b) ⊛ conj (c -ᴬ d) ≐
  (+ 2) ·ᴬ (a ⊛ conj c +ᴬ b ⊛ conj d)
⊛-conj-parallelogram a b c d i =
  trans (cong₂ _+_ plus minus)
        (law ((a ⊛ conj c) i) ((a ⊛ conj d) i)
             ((b ⊛ conj c) i) ((b ⊛ conj d) i))
  where
  law : ∀ p q r s →
        ((p + q) + (r + s)) + ((p - q) - (r - s)) ≡ (+ 2) * (p + s)
  law = solve 4 (λ p q r s →
    ((p :+ q) :+ (r :+ s)) :+ ((p :- q) :- (r :- s)) :=
    con (+ 2) :* (p :+ s)) refl

  plus : ((a +ᴬ b) ⊛ conj (c +ᴬ d)) i ≡
         ((a ⊛ conj c) i + (a ⊛ conj d) i) +
         ((b ⊛ conj c) i + (b ⊛ conj d) i)
  plus = trans
    (⊛-cong {a = a +ᴬ b} {a′ = a +ᴬ b} (λ _ → refl) (conj-+ᴬ c d) i)
    (trans (⊛-distribʳ-+ᴬ a b (conj c +ᴬ conj d) i)
           (cong₂ _+_ (⊛-distribˡ-+ᴬ a (conj c) (conj d) i)
                      (⊛-distribˡ-+ᴬ b (conj c) (conj d) i)))

  minus : ((a -ᴬ b) ⊛ conj (c -ᴬ d)) i ≡
          ((a ⊛ conj c) i - (a ⊛ conj d) i) -
          ((b ⊛ conj c) i - (b ⊛ conj d) i)
  minus = trans
    (⊛-cong {a = a -ᴬ b} {a′ = a -ᴬ b} (λ _ → refl) (conj-diff c d) i)
    (trans (⊛-distribʳ-diff a b (conj c -ᴬ conj d) i)
           (cong₂ _-_ (⊛-distribˡ-diff a (conj c) (conj d) i)
                      (⊛-distribˡ-diff b (conj c) (conj d) i)))


------------------------------------------------------------------------
-- The normalisation √2

-- √2 · a = ζ^c · a + ζ^(-c) · a passes through a product on either
-- side, a rotation at a time; so, √2 being real, the product of √2·a
-- with the conjugate of √2·b is √2 · √2 = 2 times a · b̄.  This is what
-- makes definition 2.4, stated on the operator with its normalisation
-- cleared, a property of the operator (PathSum.PartialIsometry).

√2·-⊛ˡ : ∀ a b → √2· a ⊛ b ≐ √2· (a ⊛ b)
√2·-⊛ˡ a b i =
  trans (⊛-distribʳ-+ᴬ (rot (+ c) a) (rot (- (+ c)) a) b i)
        (cong₂ _+_ (⊛-rotˡ (+ c) a b i) (⊛-rotˡ (- (+ c)) a b i))

√2·-⊛ʳ : ∀ a b → a ⊛ √2· b ≐ √2· (a ⊛ b)
√2·-⊛ʳ a b i =
  trans (⊛-distribˡ-+ᴬ a (rot (+ c) b) (rot (- (+ c)) b) i)
        (cong₂ _+_ (⊛-rotʳ (+ c) a b i) (⊛-rotʳ (- (+ c)) a b i))

⊛-conj-√2 : ∀ a b → √2· a ⊛ conj (√2· b) ≐ (+ 2) ·ᴬ (a ⊛ conj b)
⊛-conj-√2 a b i =
  trans (⊛-cong {a = √2· a} {a′ = √2· a} (λ _ → refl) (conj-√2 b) i)
    (trans (√2·-⊛ˡ a (√2· (conj b)) i)
      (trans (√2·-map (√2·-⊛ʳ a (conj b)) i)
             (√2·-twice (a ⊛ conj b) i)))
