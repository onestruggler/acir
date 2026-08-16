------------------------------------------------------------------------
-- Presentations of groups
--
-- The cyclotomic integers Z[ζ], for ζ a primitive 2^M-th root of
-- unity, in which the amplitudes of a path-sum live
--
-- An amplitude of a Clifford+R_k path-sum is a Z-linear combination
-- of the numbers e^{2πi(a/2^M)} = ζ^a, so no analysis is needed to
-- give path-sums a denotation: it is enough to compute in Z[ζ].  As
-- 2^M is a prime power the minimal polynomial of ζ is X^H + 1 with
-- H = 2^(M-1), so Z[ζ] is the free Z-module on ζ^0 … ζ^(H-1), and the
-- single relation ζ^H = -1 is what makes destructive interference
-- happen.  The module is parameterised by M₀ with M = 3 + M₀, three
-- dyadic digits being what an order-2 phase can use.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cyclotomic (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; toℕ-injective)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_; ∣_∣; _⊖_; NonZero)
open import Data.Integer.DivMod using (_/_; _%_; n%d<d; a≡a%n+[a/n]*n)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣-refl; ∣ᵤ⇒∣; ∣⇒∣ᵤ; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n;
   ∣m+n∣m⇒∣n; ∣m+n∣n⇒∣m)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; neg-involutive;
   neg-distrib-+; neg-distribʳ-*; *-distribˡ-+; pos-+; *-cancelˡ-≡;
   ∣i∣≡0⇒i≡0; [+m]-[+n]≡m⊖n;
   i-j≡0⇒i≡j; [1+m]⊖[1+n]≡m⊖n)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _≤_; _<_; _∸_; s≤s)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _^_ to _ℕ^_; _⊔_ to _ℕ⊔_;
            ≢-nonZero to ≢-nonZeroℕ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq
import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)


------------------------------------------------------------------------
-- The ring

-- H is the rank of Z[ζ] over Z, N = 2H the order of ζ, and c = N/8
-- the exponent with ζ^c + ζ^(-c) = √2.

H N c : ℕ
H = 2 ℕ^ (2 ℕ+ M₀)
N = 2 ℕ* H
c = 2 ℕ^ M₀

Amp : Set
Amp = Fin H → ℤ

infixl 6 _+ᴬ_ _-ᴬ_
infixl 7 _·ᴬ_

0ᴬ : Amp
0ᴬ _ = 0ℤ

_+ᴬ_ : Amp → Amp → Amp
(a +ᴬ b) i = a i + b i

_-ᴬ_ : Amp → Amp → Amp
(a -ᴬ b) i = a i - b i

-ᴬ_ : Amp → Amp
(-ᴬ a) i = - a i

_·ᴬ_ : ℤ → Amp → Amp
(z ·ᴬ a) i = z * a i

-- Equality of amplitudes is equality of coordinates.

infix 4 _≐_

_≐_ : Amp → Amp → Set
a ≐ b = ∀ i → a i ≡ b i


------------------------------------------------------------------------
-- Sums over Boolean assignments

-- Every sum in a path-sum ranges over the assignments to a fixed
-- number of Boolean variables.

extend : ∀ {k} → Bool → (Fin k → Bool) → (Fin (suc k) → Bool)
extend b g zero    = b
extend b g (suc i) = g i

Σᴮ : ∀ {k} → ((Fin k → Bool) → Amp) → Amp
Σᴮ {zero}  f = f (λ ())
Σᴮ {suc k} f = Σᴮ (λ g → f (extend true g)) +ᴬ Σᴮ (λ g → f (extend false g))

Σᴮ-cong : ∀ {k} {f g : (Fin k → Bool) → Amp} →
          (∀ h → f h ≐ g h) → Σᴮ f ≐ Σᴮ g
Σᴮ-cong {zero}  f≐g i = f≐g (λ ()) i
Σᴮ-cong {suc k} f≐g i = Eq.cong₂ _+_
  (Σᴮ-cong (λ h → f≐g (extend true h)) i)
  (Σᴮ-cong (λ h → f≐g (extend false h)) i)


------------------------------------------------------------------------
-- Powers of ζ

-- ζ^e is a signed basis vector: its i-th coordinate is 1 when
-- e ≡ i, is -1 when e ≡ i + H, and is 0 otherwise, all modulo N.
-- Congruences are used rather than a remainder function so that the
-- proofs below are divisibility algebra.

χ : ℤ → ℤ
χ z = if ⌊ (+ N) ∣? z ⌋ then 1ℤ
      else if ⌊ (+ N) ∣? (z - (+ H)) ⌋ then - 1ℤ
      else 0ℤ

zpow : ℤ → Amp
zpow e i = χ (e - (+ toℕ i))

private
  H>0 : 0 < H
  H>0 = 2^k>0 (2 ℕ+ M₀)
    where
    2^k>0 : ∀ k → 0 < 2 ℕ^ k
    2^k>0 zero    = ℕ.≤-refl
    2^k>0 (suc k) = ℕ.≤-trans (2^k>0 k) (ℕ.m≤m+n (2 ℕ^ k) _)

  H<N : H < N
  H<N = ℕ.m<m+n H (ℕ.≤-trans H>0 (ℕ.≤-reflexive (sym (ℕ.+-identityʳ H))))

  N≡H+H : N ≡ H ℕ+ H
  N≡H+H = cong (H ℕ+_) (ℕ.+-identityʳ H)

  -- N does not divide H, so the two branches of χ exclude each other.
  N∤H : ¬ ((+ N) ∣ (+ H))
  N∤H d with ∣⇒∣ᵤ d
  ... | ℕDiv.divides zero    eq = contradiction eq (ℕ.>⇒≢ H>0)
  ... | ℕDiv.divides (suc q) eq = contradiction
        (ℕ.≤-trans (ℕ.m≤m+n N (q ℕ* N)) (ℕ.≤-reflexive (sym eq)))
        (ℕ.<⇒≱ H<N)

  -- N ∣ (z + H) and N ∣ (z - H) are interchangeable: they differ by N.
  N∣H+H : (+ N) ∣ ((+ H) + (+ H))
  N∣H+H = Eq.subst ((+ N) ∣_) (trans (cong +_ N≡H+H) (pos-+ H H)) ∣-refl

  shift⁺ : ∀ z → (+ N) ∣ (z - (+ H)) → (+ N) ∣ (z + (+ H))
  shift⁺ z d = Eq.subst ((+ N) ∣_) (regroup z (+ H))
                          (∣m∣n⇒∣m+n d N∣H+H)
    where
    regroup : ∀ u v → (u - v) + (v + v) ≡ u + v
    regroup = solve 2 (λ u v → (u :- v) :+ (v :+ v) := u :+ v) refl

  shift⁻ : ∀ z → (+ N) ∣ (z + (+ H)) → (+ N) ∣ (z - (+ H))
  shift⁻ z d = Eq.subst ((+ N) ∣_) (regroup z (+ H))
                          (∣m∣n⇒∣m-n d N∣H+H)
    where
    regroup : ∀ u v → (u + v) - (v + v) ≡ u - v
    regroup = solve 2 (λ u v → (u :+ v) :- (v :+ v) := u :- v) refl

  +-cancel : ∀ u v → (u + v) - v ≡ u
  +-cancel = solve 2 (λ u v → (u :+ v) :- v := u) refl

  +-diff : ∀ u v → (u + v) - u ≡ v
  +-diff = solve 2 (λ u v → (u :+ v) :- u := v) refl

-- The three branches of χ, as usable equations.

χ-1 : ∀ {z} → (+ N) ∣ z → χ z ≡ 1ℤ
χ-1 {z} d with (+ N) ∣? z
... | yes _  = refl
... | no  ¬d = contradiction d ¬d

χ--1 : ∀ {z} → ¬ ((+ N) ∣ z) → (+ N) ∣ (z - (+ H)) → χ z ≡ - 1ℤ
χ--1 {z} ¬d b with (+ N) ∣? z
... | yes d = contradiction d ¬d
... | no  _ with (+ N) ∣? (z - (+ H))
...   | yes _  = refl
...   | no  ¬b = contradiction b ¬b

χ-0 : ∀ {z} → ¬ ((+ N) ∣ z) → ¬ ((+ N) ∣ (z - (+ H))) → χ z ≡ 0ℤ
χ-0 {z} ¬d ¬b with (+ N) ∣? z
... | yes d = contradiction d ¬d
... | no  _ with (+ N) ∣? (z - (+ H))
...   | yes b = contradiction b ¬b
...   | no  _ = refl

-- ζ^(z + H) = -ζ^z: the defining relation of the ring.

-- The decisions are taken as arguments rather than by `with`: the
-- statement mentions χ at two different exponents, and only one of
-- them would be abstracted.

private
  χ-anti-aux : ∀ z → Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ H))) →
               χ (z + (+ H)) ≡ - (χ z)
  χ-anti-aux z (yes d) _ = trans (χ--1 ¬A₁ B₁) (cong -_ (sym (χ-1 {z} d)))
    where
    ¬A₁ : ¬ ((+ N) ∣ (z + (+ H)))
    ¬A₁ d₁ = N∤H (Eq.subst ((+ N) ∣_) (+-diff z (+ H)) (∣m∣n⇒∣m-n d₁ d))

    B₁ : (+ N) ∣ ((z + (+ H)) - (+ H))
    B₁ = Eq.subst ((+ N) ∣_) (sym (+-cancel z (+ H))) d
  χ-anti-aux z (no ¬d) (yes b) =
    trans (χ-1 (shift⁺ z b)) (cong -_ (sym (χ--1 {z} ¬d b)))
  χ-anti-aux z (no ¬d) (no ¬b) =
    trans (χ-0 ¬A₁ ¬B₁) (cong -_ (sym (χ-0 {z} ¬d ¬b)))
    where
    ¬A₁ : ¬ ((+ N) ∣ (z + (+ H)))
    ¬A₁ d₁ = ¬b (shift⁻ z d₁)

    ¬B₁ : ¬ ((+ N) ∣ ((z + (+ H)) - (+ H)))
    ¬B₁ b₁ = ¬d (Eq.subst ((+ N) ∣_) (+-cancel z (+ H)) b₁)

χ-anti : ∀ z → χ (z + (+ H)) ≡ - (χ z)
χ-anti z = χ-anti-aux z ((+ N) ∣? z) ((+ N) ∣? (z - (+ H)))

-- χ, and hence ζ^_, only depends on the exponent modulo N.

χ-cong : ∀ {z z′} → (+ N) ∣ (z - z′) → χ z ≡ χ z′
χ-cong {z} {z′} d with (+ N) ∣? z | (+ N) ∣? z′
... | yes _  | yes _  = refl
... | yes dz | no ¬dz′ = contradiction (Eq.subst ((+ N) ∣_) (cancel z z′)
                           (∣m∣n⇒∣m-n dz d)) ¬dz′
  where
  cancel : ∀ u v → u - (u - v) ≡ v
  cancel = solve 2 (λ u v → u :- (u :- v) := v) refl
... | no ¬dz | yes dz′ = contradiction (Eq.subst ((+ N) ∣_) (restore z z′)
                           (∣m∣n⇒∣m+n dz′ d)) ¬dz
  where
  restore : ∀ u v → v + (u - v) ≡ u
  restore = solve 2 (λ u v → v :+ (u :- v) := u) refl
... | no _   | no _ with (+ N) ∣? (z - (+ H)) | (+ N) ∣? (z′ - (+ H))
...   | yes _  | yes _   = refl
...   | yes bz | no ¬bz′ = contradiction (Eq.subst ((+ N) ∣_) (down z z′ (+ H))
                             (∣m∣n⇒∣m-n bz d)) ¬bz′
  where
  down : ∀ u v w → (u - w) - (u - v) ≡ v - w
  down = solve 3 (λ u v w → (u :- w) :- (u :- v) := v :- w) refl
...   | no ¬bz | yes bz′ = contradiction (Eq.subst ((+ N) ∣_) (up z z′ (+ H))
                             (∣m∣n⇒∣m+n bz′ d)) ¬bz
  where
  up : ∀ u v w → (v - w) + (u - v) ≡ u - w
  up = solve 3 (λ u v w → (v :- w) :+ (u :- v) := u :- w) refl
...   | no _   | no _    = refl


------------------------------------------------------------------------
-- The exponent calculus of ζ

zpow-anti : ∀ e → zpow (e + (+ H)) ≐ -ᴬ (zpow e)
zpow-anti e i = trans (cong χ (regroup e (+ H) (+ toℕ i)))
                      (χ-anti (e - (+ toℕ i)))
  where
  regroup : ∀ u v w → (u + v) - w ≡ (u - w) + v
  regroup = solve 3 (λ u v w → (u :+ v) :- w := (u :- w) :+ v) refl

zpow-cong : ∀ {e e′} → (+ N) ∣ (e - e′) → zpow e ≐ zpow e′
zpow-cong {e} {e′} d i =
  χ-cong (Eq.subst ((+ N) ∣_) (regroup e e′ (+ toℕ i)) d)
  where
  regroup : ∀ u v w → u - v ≡ (u - w) - (v - w)
  regroup = solve 3 (λ u v w → u :- v := (u :- w) :- (v :- w)) refl


------------------------------------------------------------------------
-- Reducing an exponent to the basis

-- Modulo N every exponent is a basis exponent, or a basis exponent
-- shifted by H -- in which case ζ picks up a sign.

data Class (w : ℤ) : Set where
  pos : (i : Fin H) → (+ N) ∣ (w - (+ toℕ i)) → Class w
  neg : (i : Fin H) → (+ N) ∣ (w - ((+ toℕ i) + (+ H))) → Class w

private
  0<N : 0 < N
  0<N = ℕ.≤-trans H>0 (ℕ.m≤m+n H (H ℕ+ 0))

  instance
    +N-nonZero : NonZero (+ N)
    +N-nonZero = ≢-nonZeroℕ (ℕ.>⇒≢ 0<N)

  mod-∣ : ∀ w → (+ N) ∣ (w - (+ (w % (+ N))))
  mod-∣ w = divides (w / (+ N)) eq
    where
    eq : w - (+ (w % (+ N))) ≡ (w / (+ N)) * (+ N)
    eq = trans (cong (_- (+ (w % (+ N)))) (a≡a%n+[a/n]*n w (+ N)))
               (+-diff (+ (w % (+ N))) ((w / (+ N)) * (+ N)))

classify : ∀ w → Class w
classify w with w % (+ N) | n%d<d w (+ N) | mod-∣ w
... | r | r<N | d with r ℕ.<? H
...   | yes r<H = pos (fromℕ< r<H)
        (Eq.subst (λ u → (+ N) ∣ (w - (+ u))) (sym (toℕ-fromℕ< r<H)) d)
...   | no ¬r<H = neg (fromℕ< r∸H<H)
        (Eq.subst (λ u → (+ N) ∣ (w - u)) split d)
  where
  H≤r : H ≤ r
  H≤r = ℕ.≮⇒≥ ¬r<H

  r∸H<H : r ∸ H < H
  r∸H<H = Eq.subst (r ∸ H <_) (ℕ.m+n∸n≡m H H)
    (ℕ.∸-monoˡ-< (Eq.subst (r <_) N≡H+H r<N) H≤r)

  split : (+ r) ≡ (+ toℕ (fromℕ< r∸H<H)) + (+ H)
  split = sym (trans (cong (λ u → (+ u) + (+ H)) (toℕ-fromℕ< r∸H<H))
    (trans (sym (pos-+ (r ∸ H) H)) (cong +_ (ℕ.m∸n+n≡m H≤r))))


------------------------------------------------------------------------
-- Uniqueness of the reduction

private
  ∣⊖∣≤⊔ : ∀ a b → (∣ a ⊖ b ∣) ≤ a ℕ⊔ b
  ∣⊖∣≤⊔ a       zero    = ℕ.≤-reflexive (sym (ℕ.⊔-identityʳ a))
  ∣⊖∣≤⊔ zero    (suc b) = ℕ.≤-refl
  ∣⊖∣≤⊔ (suc a) (suc b) = ℕ.≤-trans
    (ℕ.≤-reflexive (cong ∣_∣ ([1+m]⊖[1+n]≡m⊖n a b)))
    (ℕ.≤-trans (∣⊖∣≤⊔ a b) (ℕ.n≤1+n _))

  bounded : ∀ {z} → (+ N) ∣ z → (∣ z ∣) < N → z ≡ 0ℤ
  bounded d lt with ∣⇒∣ᵤ d
  ... | ℕDiv.divides zero    eq = ∣i∣≡0⇒i≡0 eq
  ... | ℕDiv.divides (suc q) eq = contradiction
        (ℕ.≤-trans (ℕ.m≤m+n N (q ℕ* N)) (ℕ.≤-reflexive (sym eq)))
        (ℕ.<⇒≱ lt)

  diff-bound : ∀ a b → a < N → b < N → (∣ (+ a) - (+ b) ∣) < N
  diff-bound a b a<N b<N = ℕ.≤-trans
    (s≤s (ℕ.≤-trans
      (ℕ.≤-reflexive (cong ∣_∣ ([+m]-[+n]≡m⊖n a b))) (∣⊖∣≤⊔ a b)))
    (ℕ.⊔-lub a<N b<N)

  i<N : ∀ (i : Fin H) → toℕ i < N
  i<N i = ℕ.<-trans (toℕ<n i) H<N

  diff≡0 : ∀ u (a b : ℕ) → a < N → b < N →
           (+ N) ∣ (u - (+ a)) → (+ N) ∣ (u - (+ b)) → a ≡ b
  diff≡0 u a b a<N b<N da db = sym (cong ∣_∣ (i-j≡0⇒i≡j (+ b) (+ a)
    (bounded (Eq.subst ((+ N) ∣_) (regroup u (+ a) (+ b))
                       (∣m∣n⇒∣m-n da db))
             (diff-bound b a b<N a<N))))
    where
    regroup : ∀ x y z → (x - y) - (x - z) ≡ z - y
    regroup = solve 3 (λ x y z → (x :- y) :- (x :- z) := z :- y) refl

uniq : ∀ u (i j : Fin H) → (+ N) ∣ (u - (+ toℕ i)) →
       (+ N) ∣ (u - (+ toℕ j)) → i ≡ j
uniq u i j di dj =
  toℕ-injective (diff≡0 u (toℕ i) (toℕ j) (i<N i) (i<N j) di dj)

cross : ∀ u (i j : Fin H) → (+ N) ∣ (u - (+ toℕ i)) →
        (+ N) ∣ (u - ((+ toℕ j) + (+ H))) → ⊥
cross u i j di dj = contradiction
  (diff≡0 u (toℕ i) (toℕ j ℕ+ H) (i<N i) j+H<N di
    (Eq.subst (λ v → (+ N) ∣ (u - v)) (sym (pos-+ (toℕ j) H)) dj))
  (ℕ.<⇒≢ (ℕ.<-≤-trans (toℕ<n i) (ℕ.m≤n+m H (toℕ j))))
  where
  j+H<N : toℕ j ℕ+ H < N
  j+H<N = Eq.subst (toℕ j ℕ+ H <_) (sym N≡H+H)
    (ℕ.+-monoˡ-< H (toℕ<n j))


------------------------------------------------------------------------
-- Coefficients at an arbitrary exponent

private
  ∣0 : ∀ {i} → i ∣ 0ℤ
  ∣0 = ∣ᵤ⇒∣ (ℕDiv.divides 0 refl)

  self : ∀ x → (+ N) ∣ (x - x)
  self x = Eq.subst ((+ N) ∣_) (sym (x-x x)) ∣0
    where
    x-x : ∀ u → u - u ≡ 0ℤ
    x-x = solve 1 (λ u → u :- u := con (+ 0)) refl

  -- Moving the shift by H between the exponent and the index.

  neg→pos : ∀ w (i : Fin H) → (+ N) ∣ (w - ((+ toℕ i) + (+ H))) →
            (+ N) ∣ ((w + (+ H)) - (+ toℕ i))
  neg→pos w i d = Eq.subst ((+ N) ∣_) (shape w (+ toℕ i) (+ H))
                             (∣m∣n⇒∣m+n d N∣H+H)
    where
    shape : ∀ u v t → (u - (v + t)) + (t + t) ≡ (u + t) - v
    shape = solve 3 (λ u v t → (u :- (v :+ t)) :+ (t :+ t) := (u :+ t) :- v)
              refl

  pos→neg : ∀ w (i : Fin H) → (+ N) ∣ ((w + (+ H)) - (+ toℕ i)) →
            (+ N) ∣ (w - ((+ toℕ i) + (+ H)))
  pos→neg w i d = Eq.subst ((+ N) ∣_) (shape w (+ toℕ i) (+ H))
                             (∣m∣n⇒∣m-n d N∣H+H)
    where
    shape : ∀ u v t → ((u + t) - v) - (t + t) ≡ u - (v + t)
    shape = solve 3 (λ u v t → ((u :+ t) :- v) :- (t :+ t) := u :- (v :+ t))
              refl

  drop-H : ∀ w (i : Fin H) → (+ N) ∣ ((w + (+ H)) - ((+ toℕ i) + (+ H))) →
           (+ N) ∣ (w - (+ toℕ i))
  drop-H w i = Eq.subst ((+ N) ∣_) (shape w (+ toℕ i) (+ H))
    where
    shape : ∀ u v t → ((u + t) - (v + t)) ≡ u - v
    shape = solve 3 (λ u v t → (u :+ t) :- (v :+ t) := u :- v) refl

  transport : ∀ w w′ v → (+ N) ∣ (w - w′) → (+ N) ∣ (w′ - v) →
              (+ N) ∣ (w - v)
  transport w w′ v d e = Eq.subst ((+ N) ∣_) (shape w w′ v)
                                        (∣m∣n⇒∣m+n d e)
    where
    shape : ∀ u u′ t → (u - u′) + (u′ - t) ≡ u - t
    shape = solve 3 (λ u u′ t → (u :- u′) :+ (u′ :- t) := u :- t) refl

  coeff-aux : Amp → ∀ {w} → Class w → ℤ
  coeff-aux a (pos i _) = a i
  coeff-aux a (neg i _) = - a i

-- The coefficient of ζ^w in a, for an arbitrary integer exponent w.

coeff : Amp → ℤ → ℤ
coeff a w = coeff-aux a (classify w)

coeff-δ : ∀ a i → coeff a (+ toℕ i) ≡ a i
coeff-δ a i with classify (+ toℕ i)
... | pos j d = cong a (uniq (+ toℕ i) j i d (self (+ toℕ i)))
... | neg j d = ⊥-elim (cross (+ toℕ i) i j (self (+ toℕ i)) d)

coeff-cong : ∀ a w w′ → (+ N) ∣ (w - w′) → coeff a w ≡ coeff a w′
coeff-cong a w w′ d with classify w | classify w′
... | pos i di | pos j dj =
      cong a (uniq w i j di (transport w w′ (+ toℕ j) d dj))
... | pos i di | neg j dj =
      ⊥-elim (cross w i j di (transport w w′ _ d dj))
... | neg i di | pos j dj =
      ⊥-elim (cross w j i (transport w w′ (+ toℕ j) d dj) di)
... | neg i di | neg j dj = cong -_ (cong a
      (uniq (w + (+ H)) i j (neg→pos w i di)
        (neg→pos w j (transport w w′ _ d dj))))

coeff-anti : ∀ a w → coeff a (w + (+ H)) ≡ - (coeff a w)
coeff-anti a w with classify (w + (+ H)) | classify w
... | pos i di | pos j dj = ⊥-elim (cross w j i dj (pos→neg w i di))
... | pos i di | neg j dj =
      trans (cong a (uniq (w + (+ H)) i j di (neg→pos w j dj)))
            (sym (neg-involutive (a j)))
... | neg i di | pos j dj = cong -_ (cong a (uniq w i j (drop-H w i di) dj))
... | neg i di | neg j dj = ⊥-elim (cross w i j (drop-H w i di) dj)

coeff-map : ∀ {a b} → a ≐ b → ∀ w → coeff a w ≡ coeff b w
coeff-map a≐b w with classify w
... | pos i _ = a≐b i
... | neg i _ = cong -_ (a≐b i)

coeff-+ : ∀ a b w → coeff (a +ᴬ b) w ≡ coeff a w + coeff b w
coeff-+ a b w with classify w
... | pos i _ = refl
... | neg i _ = neg-distrib-+ (a i) (b i)


------------------------------------------------------------------------
-- Multiplication by a root of unity

-- The coefficient of ζ^i in ζ^e · a is the coefficient of ζ^(i-e)
-- in a.

rot : ℤ → Amp → Amp
rot e a i = coeff a ((+ toℕ i) - e)

rot-map : ∀ {a b} e → a ≐ b → rot e a ≐ rot e b
rot-map e a≐b i = coeff-map a≐b ((+ toℕ i) - e)

rot-exp : ∀ {e e′} a → e ≡ e′ → rot e a ≐ rot e′ a
rot-exp a refl _ = refl

rot-0 : ∀ a → rot 0ℤ a ≐ a
rot-0 a i = trans (cong (coeff a) (+-identityʳ (+ toℕ i))) (coeff-δ a i)

rot-+ᴬ : ∀ e a b → rot e (a +ᴬ b) ≐ rot e a +ᴬ rot e b
rot-+ᴬ e a b i = coeff-+ a b ((+ toℕ i) - e)

rot-anti : ∀ e a → rot (e + (+ H)) a ≐ -ᴬ (rot e a)
rot-anti e a i = trans (cong (coeff a) (shape (+ toℕ i) e (+ H))) flip
  where
  shape : ∀ u v t → u - (v + t) ≡ (u - v) - t
  shape = solve 3 (λ u v t → u :- (v :+ t) := (u :- v) :- t) refl

  raise : ∀ u v t → ((u - v) - t) + t ≡ u - v
  raise = solve 3 (λ u v t → ((u :- v) :- t) :+ t := u :- v) refl

  up : coeff a ((+ toℕ i) - e) ≡ - (coeff a (((+ toℕ i) - e) - (+ H)))
  up = trans (cong (coeff a) (sym (raise (+ toℕ i) e (+ H))))
             (coeff-anti a (((+ toℕ i) - e) - (+ H)))

  flip : coeff a (((+ toℕ i) - e) - (+ H)) ≡ - (coeff a ((+ toℕ i) - e))
  flip = trans (sym (neg-involutive _)) (cong -_ (sym up))

-- The coefficient of ζ^w in ζ^e is 1, -1 or 0 according as e and w
-- agree modulo N, differ by H, or neither.

coeff-zpow : ∀ e w → coeff (zpow e) w ≡ χ (e - w)
coeff-zpow e w with classify w
... | pos i d = χ-cong (Eq.subst ((+ N) ∣_)
      (sym (shape e (+ toℕ i) w)) d)
  where
  shape : ∀ u v t → (u - v) - (u - t) ≡ t - v
  shape = solve 3 (λ u v t → (u :- v) :- (u :- t) := t :- v) refl
... | neg i d = trans (sym flip) (χ-cong shifted)
  where
  shape : ∀ u v s t → t - (v + s) ≡ ((u - v) - s) - (u - t)
  shape = solve 4 (λ u v s t →
    t :- (v :+ s) := ((u :- v) :- s) :- (u :- t)) refl

  shifted : (+ N) ∣ (((e - (+ toℕ i)) - (+ H)) - (e - w))
  shifted = Eq.subst ((+ N) ∣_) (shape e (+ toℕ i) (+ H) w) d

  raise : ∀ u v s → ((u - v) - s) + s ≡ u - v
  raise = solve 3 (λ u v s → ((u :- v) :- s) :+ s := u :- v) refl

  flip : χ ((e - (+ toℕ i)) - (+ H)) ≡ - (χ (e - (+ toℕ i)))
  flip = trans (sym (neg-involutive _))
    (cong -_ (sym (trans (cong χ (sym (raise e (+ toℕ i) (+ H))))
                         (χ-anti ((e - (+ toℕ i)) - (+ H))))))

rot-zpow : ∀ e′ e → rot e′ (zpow e) ≐ zpow (e′ + e)
rot-zpow e′ e i = trans (coeff-zpow e ((+ toℕ i) - e′))
                        (cong χ (shape e e′ (+ toℕ i)))
  where
  shape : ∀ u v t → u - (t - v) ≡ (v + u) - t
  shape = solve 3 (λ u v t → u :- (t :- v) := (v :+ u) :- t) refl

rot-comp : ∀ e e′ a → rot e (rot e′ a) ≐ rot (e + e′) a
rot-comp e e′ a i with classify ((+ toℕ i) - e)
... | pos j d = sym (coeff-cong a ((+ toℕ i) - (e + e′)) ((+ toℕ j) - e′)
      (Eq.subst ((+ N) ∣_) (shape (+ toℕ i) (+ toℕ j) e e′) d))
  where
  shape : ∀ u v y y′ → (u - y) - v ≡ (u - (y + y′)) - (v - y′)
  shape = solve 4 (λ u v y y′ →
    (u :- y) :- v := (u :- (y :+ y′)) :- (v :- y′)) refl
... | neg j d = sym (trans
      (coeff-cong a ((+ toℕ i) - (e + e′)) (((+ toℕ j) - e′) + (+ H))
        (Eq.subst ((+ N) ∣_) (shape (+ toℕ i) (+ toℕ j) e e′ (+ H)) d))
      (coeff-anti a ((+ toℕ j) - e′)))
  where
  shape : ∀ u v y y′ t →
          ((u - y) - (v + t)) ≡ (u - (y + y′)) - ((v - y′) + t)
  shape = solve 5 (λ u v y y′ t →
    (u :- y) :- (v :+ t) := (u :- (y :+ y′)) :- ((v :- y′) :+ t)) refl


------------------------------------------------------------------------
-- Multiplication by √2

-- √2 = ζ^(N/8) + ζ^(-N/8), and c = N/8.

√2· : Amp → Amp
√2· a = rot (+ c) a +ᴬ rot (- (+ c)) a

scale : ℕ → Amp → Amp
scale zero    a = a
scale (suc j) a = √2· (scale j a)

coeff-·ᴬ : ∀ (z : ℤ) a w → coeff (z ·ᴬ a) w ≡ z * coeff a w
coeff-·ᴬ z a w with classify w
... | pos i _ = refl
... | neg i _ = neg-distribʳ-* z (a i)

rot-·ᴬ : ∀ e (z : ℤ) a → rot e (z ·ᴬ a) ≐ z ·ᴬ rot e a
rot-·ᴬ e z a i = coeff-·ᴬ z a ((+ toℕ i) - e)

√2·-map : ∀ {a b} → a ≐ b → √2· a ≐ √2· b
√2·-map a≐b i = Eq.cong₂ _+_ (rot-map (+ c) a≐b i) (rot-map (- (+ c)) a≐b i)

scale-map : ∀ j {a b} → a ≐ b → scale j a ≐ scale j b
scale-map zero    a≐b = a≐b
scale-map (suc j) a≐b = √2·-map (scale-map j a≐b)

+ᴬ-comm : ∀ a b → a +ᴬ b ≐ b +ᴬ a
+ᴬ-comm a b i = +-comm (a i) (b i)

rot-0ᴬ : ∀ e → rot e 0ᴬ ≐ 0ᴬ
rot-0ᴬ e i with classify ((+ toℕ i) - e)
... | pos _ _ = refl
... | neg _ _ = refl

Σᴮ-+ : ∀ {k} (f g : (Fin k → Bool) → Amp) →
       Σᴮ (λ y → f y +ᴬ g y) ≐ Σᴮ f +ᴬ Σᴮ g
Σᴮ-+ {zero}  f g i = refl
Σᴮ-+ {suc k} f g i = trans
  (Eq.cong₂ _+_
    (Σᴮ-+ (λ y → f (extend true y)) (λ y → g (extend true y)) i)
    (Σᴮ-+ (λ y → f (extend false y)) (λ y → g (extend false y)) i))
  (shuffle (Σᴮ (λ y → f (extend true y)) i)
           (Σᴮ (λ y → g (extend true y)) i)
           (Σᴮ (λ y → f (extend false y)) i)
           (Σᴮ (λ y → g (extend false y)) i))
  where
  shuffle : ∀ p q r s → (p + q) + (r + s) ≡ (p + r) + (q + s)
  shuffle = solve 4 (λ p q r s →
    (p :+ q) :+ (r :+ s) := (p :+ r) :+ (q :+ s)) refl

rot-Σᴮ : ∀ {k} e (f : (Fin k → Bool) → Amp) →
         rot e (Σᴮ f) ≐ Σᴮ (λ y → rot e (f y))
rot-Σᴮ {zero}  e f i = refl
rot-Σᴮ {suc k} e f i = trans
  (rot-+ᴬ e (Σᴮ (λ y → f (extend true y)))
            (Σᴮ (λ y → f (extend false y))) i)
  (Eq.cong₂ _+_ (rot-Σᴮ e (λ y → f (extend true y)) i)
                (rot-Σᴮ e (λ y → f (extend false y)) i))

-- Multiplying a single power of ζ by √2 splits it in two.

√2·-zpow : ∀ e → √2· (zpow e) ≐ zpow ((+ c) + e) +ᴬ zpow ((- (+ c)) + e)
√2·-zpow e i =
  Eq.cong₂ _+_ (rot-zpow (+ c) e i) (rot-zpow (- (+ c)) e i)

scale-√2 : ∀ j a → scale j (√2· a) ≐ √2· (scale j a)
scale-√2 zero    a _ = refl
scale-√2 (suc j) a   = √2·-map (scale-√2 j a)

√2·-0ᴬ : √2· 0ᴬ ≐ 0ᴬ
√2·-0ᴬ i = Eq.cong₂ _+_ (rot-0ᴬ (+ c) i) (rot-0ᴬ (- (+ c)) i)

√2·-Σᴮ : ∀ {k} (f : (Fin k → Bool) → Amp) →
         √2· (Σᴮ f) ≐ Σᴮ (λ y → √2· (f y))
√2·-Σᴮ f i = trans
  (Eq.cong₂ _+_ (rot-Σᴮ (+ c) f i) (rot-Σᴮ (- (+ c)) f i))
  (sym (Σᴮ-+ (λ y → rot (+ c) (f y)) (λ y → rot (- (+ c)) (f y)) i))

√2·-·ᴬ : ∀ (z : ℤ) a → √2· (z ·ᴬ a) ≐ z ·ᴬ √2· a
√2·-·ᴬ z a i = trans
  (Eq.cong₂ _+_ (rot-·ᴬ (+ c) z a i) (rot-·ᴬ (- (+ c)) z a i))
  (sym (*-distribˡ-+ z (rot (+ c) a i) (rot (- (+ c)) a i)))

scale-·ᴬ : ∀ j (z : ℤ) a → scale j (z ·ᴬ a) ≐ z ·ᴬ scale j a
scale-·ᴬ zero    z a _ = refl
scale-·ᴬ (suc j) z a i =
  trans (√2·-map (scale-·ᴬ j z a) i) (√2·-·ᴬ z (scale j a) i)

private
  H≡4c : (+ H) ≡ ((+ c) + (+ c)) + ((+ c) + (+ c))
  H≡4c = trans (cong +_ inℕ)
    (trans (pos-+ (c ℕ+ c) (c ℕ+ c)) (Eq.cong₂ _+_ (pos-+ c c) (pos-+ c c)))
    where
    inℕ : H ≡ (c ℕ+ c) ℕ+ (c ℕ+ c)
    inℕ = trans (cong ((2 ℕ* c) ℕ+_) (ℕ.+-identityʳ (2 ℕ* c)))
                (Eq.cong₂ _ℕ+_ two two)
      where
      two : 2 ℕ* c ≡ c ℕ+ c
      two = cong (c ℕ+_) (ℕ.+-identityʳ c)

-- √2 · √2 = 2: the two cross terms are ζ^0, and ζ^(N/4) and
-- ζ^(-N/4) cancel because they differ by ζ^H = -1.

√2·-twice : ∀ a → √2· (√2· a) ≐ (+ 2) ·ᴬ a
√2·-twice a i = trans left (trans (cong (_+ (a i + a i)) cancel)
                                  (trans (+-identityˡ _) double))
  where
  P = rot ((+ c) + (+ c)) a i
  S = rot ((- (+ c)) + (- (+ c))) a i

  half : ∀ e → rot e (√2· a) i ≡ rot (e + (+ c)) a i + rot (e + (- (+ c))) a i
  half e = trans (rot-+ᴬ e (rot (+ c) a) (rot (- (+ c)) a) i)
    (Eq.cong₂ _+_ (rot-comp e (+ c) a i) (rot-comp e (- (+ c)) a i))

  mid₁ : rot ((+ c) + (- (+ c))) a i ≡ a i
  mid₁ = trans (rot-exp a (+-inverseʳ (+ c)) i) (rot-0 a i)

  mid₂ : rot ((- (+ c)) + (+ c)) a i ≡ a i
  mid₂ = trans (rot-exp a (+-inverseˡ (+ c)) i) (rot-0 a i)

  left : √2· (√2· a) i ≡ (P + S) + (a i + a i)
  left = trans (Eq.cong₂ _+_ (half (+ c)) (half (- (+ c))))
    (trans (Eq.cong₂ _+_ (cong (λ w → P + w) mid₁) (cong (_+ S) mid₂))
           (shuffle P (a i) S))
    where
    shuffle : ∀ p q s → (p + q) + (q + s) ≡ (p + s) + (q + q)
    shuffle = solve 3 (λ p q s → (p :+ q) :+ (q :+ s) := (p :+ s) :+ (q :+ q))
                refl

  cancel : P + S ≡ 0ℤ
  cancel = trans (cong (_+ S) P≡-S) (+-inverseˡ S)
    where
    P≡-S : P ≡ - S
    P≡-S = trans (rot-exp a (shape (+ c) (+ H) H≡4c) i)
                 (rot-anti ((- (+ c)) + (- (+ c))) a i)
      where
      shape : ∀ u t → t ≡ (u + u) + (u + u) →
              u + u ≡ ((- u) + (- u)) + t
      shape u t eq =
        trans (sym (lem u)) (cong (λ w → ((- u) + (- u)) + w) (sym eq))
        where
        lem : ∀ v → ((- v) + (- v)) + ((v + v) + (v + v)) ≡ v + v
        lem = solve 1 (λ v → ((:- v) :+ (:- v)) :+
                             ((v :+ v) :+ (v :+ v)) := v :+ v) refl

  double : a i + a i ≡ (+ 2) * a i
  double = twice (a i)
    where
    twice : ∀ q → q + q ≡ (+ 2) * q
    twice = solve 1 (λ q → q :+ q := con (+ 2) :* q) refl

√2·-injective : ∀ a b → √2· a ≐ √2· b → a ≐ b
√2·-injective a b eq i = *-cancelˡ-≡ (+ 2) (a i) (b i)
  (trans (sym (√2·-twice a i)) (trans (√2·-map eq i) (√2·-twice b i)))

scale-injective : ∀ j a b → scale j a ≐ scale j b → a ≐ b
scale-injective zero    a b eq = eq
scale-injective (suc j) a b eq =
  scale-injective j a b (√2·-injective (scale j a) (scale j b) eq)


------------------------------------------------------------------------
-- Splitting a sum over assignments at an index

-- The assignments giving the index false each contribute twice: once
-- as they are, and once with the index set to true.  An assignment is
-- a function, so the updated one is only pointwise equal to the one
-- the recursion produces, and the summand has to respect that.

Respects : ∀ {k} → ((Fin k → Bool) → Amp) → Set
Respects f = ∀ g h → (∀ j → g j ≡ h j) → f g ≐ f h

setᵗ : ∀ {k} → Fin k → (Fin k → Bool) → (Fin k → Bool)
setᵗ i g j = if ⌊ j Fin.≟ i ⌋ then true else g j

private
  Σᴮ-0 : ∀ {k} → Σᴮ {k} (λ _ → 0ᴬ) ≐ 0ᴬ
  Σᴮ-0 {zero}  i = refl
  Σᴮ-0 {suc k} i = Eq.cong₂ _+_ (Σᴮ-0 {k} i) (Σᴮ-0 {k} i)

  ⌊≟⌋-suc : ∀ {k} (j i : Fin k) →
            ⌊ suc j Fin.≟ suc i ⌋ ≡ ⌊ j Fin.≟ i ⌋
  ⌊≟⌋-suc j i with j Fin.≟ i
  ... | yes _ = refl
  ... | no  _ = refl

  extend-cong : ∀ {k} (b : Bool) (g h : Fin k → Bool) →
                (∀ j → g j ≡ h j) → ∀ j → extend b g j ≡ extend b h j
  extend-cong b g h g≗h zero    = refl
  extend-cong b g h g≗h (suc j) = g≗h j

Σᴮ-at : ∀ {k} (i : Fin k) (f : (Fin k → Bool) → Amp) → Respects f →
        Σᴮ f ≐ Σᴮ (λ g → if g i then 0ᴬ else (f g +ᴬ f (setᵗ i g)))
Σᴮ-at {suc k} zero f resp w = sym (trans
  (Eq.cong₂ _+_ (Σᴮ-0 {k} w)
    (trans (Σᴮ-+ (λ g → f (extend false g))
                 (λ g → f (setᵗ zero (extend false g))) w)
           (cong (λ z → Σᴮ (λ g → f (extend false g)) w + z)
             (Σᴮ-cong {f = λ g → f (setᵗ zero (extend false g))}
                      {g = λ g → f (extend true g)}
                      (λ g → resp (setᵗ zero (extend false g))
                                  (extend true g) (pt g)) w))))
  (trans (+-identityˡ (Σᴮ (λ g → f (extend false g)) w +
                       Σᴮ (λ g → f (extend true g)) w))
         (+-comm (Σᴮ (λ g → f (extend false g)) w)
                 (Σᴮ (λ g → f (extend true g)) w))))
  where
  pt : ∀ g j → setᵗ zero (extend false g) j ≡ extend true g j
  pt g zero    = refl
  pt g (suc j) = refl
Σᴮ-at {suc k} (suc i) f resp w = trans
  (Eq.cong₂ _+_
    (Σᴮ-at i (λ g → f (extend true  g)) (respExt true)  w)
    (Σᴮ-at i (λ g → f (extend false g)) (respExt false) w))
  (Eq.cong₂ _+_ (Σᴮ-cong (adjust true)  w)
                (Σᴮ-cong (adjust false) w))
  where
  respExt : ∀ b → Respects (λ g → f (extend b g))
  respExt b g h g≗h = resp (extend b g) (extend b h) (extend-cong b g h g≗h)

  pt : ∀ b g j → extend b (setᵗ i g) j ≡ setᵗ (suc i) (extend b g) j
  pt b g zero    = refl
  pt b g (suc j) =
    cong (λ t → if t then true else g j) (sym (⌊≟⌋-suc j i))

  adjust : ∀ b g →
    (if g i then 0ᴬ else
     (f (extend b g) +ᴬ f (extend b (setᵗ i g)))) ≐
    (if extend b g (suc i) then 0ᴬ else
     (f (extend b g) +ᴬ f (setᵗ (suc i) (extend b g))))
  adjust b g with g i
  ... | true  = λ _ → refl
  ... | false = λ w′ → cong (λ z → f (extend b g) w′ + z)
        (resp (extend b (setᵗ i g)) (setᵗ (suc i) (extend b g)) (pt b g) w′)


------------------------------------------------------------------------
-- ζ^0 is not zero

-- Lemma 4.2 ends by contradicting the identity's amplitude, so it
-- needs one amplitude known to be non-zero.

zpow-0≢0ᴬ : ¬ (zpow 0ℤ ≐ 0ᴬ)
zpow-0≢0ᴬ eq = contradiction (trans (sym val) (eq i₀)) λ ()
  where
  i₀ : Fin H
  i₀ = fromℕ< H>0

  N∣0 : (+ N) ∣ 0ℤ
  N∣0 = ∣ᵤ⇒∣ (ℕDiv.divides 0 refl)

  val : zpow 0ℤ i₀ ≡ 1ℤ
  val = trans (cong (λ u → χ (0ℤ - (+ u))) (toℕ-fromℕ< H>0)) (χ-1 N∣0)
