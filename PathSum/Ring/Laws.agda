------------------------------------------------------------------------
-- Presentations of groups
--
-- The ring laws of Z[ζ]: commutativity, associativity, conjugation
--
-- PathSum.Ring defines the product ⊛ of Z[ζ] as a negacyclic
-- convolution and conjugation conj as ζ ↦ ζ⁻¹, and proves the laws
-- that the Hermitian product of columns and definition 2.4 use.  This
-- module proves the rest, so that (Amp, +ᴬ, ⊛, conj) is a commutative
-- ring with involution in the sense of the standard library, equality
-- being ≐ (coordinate by coordinate):
--
--   * a ⊛ b = b ⊛ a, and so ζ^0 is a unit on the right as well;
--   * (a ⊛ b) ⊛ c = a ⊛ (b ⊛ c);
--   * conj (a ⊛ b) = conj a ⊛ conj b, so conj is a ring automorphism,
--     and an involution (PathSum.Ring's conj-involutive);
--   * ⊛ distributes over sums over assignments, both the recursive Σᴮ
--     of PathSum.Cyclotomic (which amp is built from) and the Σᵃ of
--     PathSum.Hermitian (which the Gram matrix is built from), and
--     conj commutes with Σᴮ;
--   * the normalisation √2^j passes through a product on either side,
--     and through conj.
--
-- The proofs are sums moved around.  A coefficient of a ⊛ b is the
-- window sum Σ_{j<H} a_j b_(u-j), and its summand t ↦ a_t b_(u-t) is
-- H-periodic, both factors changing sign under a shift by H.  For such
-- a summand the window can be reflected as well as moved (Σ<-reflect):
-- summed backwards, the terms g (u - j) for j < H are g (j + s) for an
-- s that PathSum.Norm's Window lemma then moves back to 0.  Reflection
-- gives commutativity (j ↦ u - j swaps the factors), and at u = 0 the
-- multiplicativity of conj.  Associativity exchanges two window sums
-- (Σ<-swap) and moves the inner window by j.
--
-- Z[ζ] is represented here by its coordinates, not as a quotient of
-- Z[X]: that ⊛ is the product of Z[X]/(X^H + 1) is the reading of the
-- convolution in PathSum.Ring's header, not a theorem; what is proved
-- is that ⊛ obeys the ring laws.  As before, conj is identified with
-- complex conjugation through an embedding Z[ζ] ↪ C that is not
-- formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ring.Laws (M₀ : ℕ) where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Morphism.Structures using (module RingMorphisms)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ;
   *-comm; *-assoc; *-zeroˡ; *-distribʳ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.Structures using (IsEquivalence)

open import PathSum.AssignSum using (Σᶻ; Σᶻ-cong; Σᶻ-+; Σᶻ-*; Σᶻ-0)
open import PathSum.Cyclotomic M₀ using
  (H; Amp; 0ᴬ; _+ᴬ_; -ᴬ_; _≐_; zpow; coeff; coeff-anti; Σᴮ; extend;
   scale; √2·-map; +ᴬ-comm)
open import PathSum.Hermitian M₀ using (Σᵃ; Σᵃ-cong; coeff-Σᵃ)
open import PathSum.Norm M₀ using
  (Σ<; Σ<-cong; Σ<-+; Σ<-*; Σ<-0; Σ<-front; module Window; neg*neg)
open import PathSum.Ring M₀ using
  (_⊛_; conj; coeff-exp; coeff-anti⁻; coeff-⊛; ⊛-cong; ⊛-distribˡ-+ᴬ;
   ⊛-distribʳ-+ᴬ; ⊛-identityˡ; coeff-conj; conj-cong; conj-involutive;
   conj-+ᴬ; conj-neg; conj-0ᴬ; conj-zpow; conj-√2; √2·-⊛ˡ; √2·-⊛ʳ)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:=_)


------------------------------------------------------------------------
-- Sums over a window

-- A factor on the right distributes over a sum, and two sums commute.

Σ<-*ʳ : ∀ k (f : ℕ → ℤ) (z : ℤ) → Σ< k f * z ≡ Σ< k (λ j → f j * z)
Σ<-*ʳ zero    f z = *-zeroˡ z
Σ<-*ʳ (suc k) f z = trans (*-distribʳ-+ z (Σ< k f) (f k))
                          (cong (_+ (f k * z)) (Σ<-*ʳ k f z))

Σ<-swap : ∀ k l (f : ℕ → ℕ → ℤ) →
          Σ< k (λ i → Σ< l (λ j → f i j)) ≡ Σ< l (λ j → Σ< k (λ i → f i j))
Σ<-swap zero    l f = sym (Σ<-0 l {f = λ _ → 0ℤ} (λ _ _ → refl))
Σ<-swap (suc k) l f =
  trans (cong (_+ Σ< l (λ j → f k j)) (Σ<-swap k l f))
        (sym (Σ<-+ l (λ j → Σ< k (λ i → f i j)) (λ j → f k j)))

-- A window summed backwards: the terms g (s - j) for j < k are the
-- terms g (j + (s - k + 1)) in the other order.  (1ℤ + + j is + suc j
-- by computation, which is what lets the solver's identities apply.)

Σ<-reverse : ∀ k (g : ℤ → ℤ) s →
             Σ< k (λ j → g (s - (+ j))) ≡
             Σ< k (λ j → g ((+ j) + ((s - (+ k)) + 1ℤ)))
Σ<-reverse zero    g s = refl
Σ<-reverse (suc k) g s = trans
  (cong (_+ g (s - (+ k))) (Σ<-reverse k g s))
  (trans (+-comm (Σ< k (λ j → g ((+ j) + ((s - (+ k)) + 1ℤ))))
                 (g (s - (+ k))))
    (sym (trans (Σ<-front k (λ j → g ((+ j) + ((s - (+ suc k)) + 1ℤ))))
           (cong₂ _+_ (cong g (bottom s (+ k)))
                      (Σ<-cong k (λ j → cong g (step (+ j) s (+ k))))))))
  where
  bottom : ∀ s t → (+ 0) + ((s - (1ℤ + t)) + 1ℤ) ≡ s - t
  bottom = solve 2 (λ s t →
    con (+ 0) :+ ((s :- (con 1ℤ :+ t)) :+ con 1ℤ) := s :- t) refl

  step : ∀ x s t → (1ℤ + x) + ((s - (1ℤ + t)) + 1ℤ) ≡ x + ((s - t) + 1ℤ)
  step = solve 3 (λ x s t →
    (con 1ℤ :+ x) :+ ((s :- (con 1ℤ :+ t)) :+ con 1ℤ) :=
    x :+ ((s :- t) :+ con 1ℤ)) refl

-- The window of an H-periodic summand can be reflected: summed
-- backwards it is a window starting at u - H + 1, which Window moves
-- back to 0.

Σ<-reflect : (g : ℤ → ℤ) → (∀ w → g (w + (+ H)) ≡ g w) →
             ∀ u → Σ< H (λ j → g (u - (+ j))) ≡ Σ< H (λ j → g (+ j))
Σ<-reflect g per u = trans (Σ<-reverse H g u)
  (trans (Window.window g per ((u - (+ H)) + 1ℤ))
         (Σ<-cong H (λ j → cong g (+-identityʳ (+ j)))))

private
  -- The convolution read at an arbitrary exponent u, as in
  -- PathSum.Ring: lemmas are proved at a variable u and used at
  -- u = + toℕ i, so that no exponent is rewritten in place.

  conv : Amp → Amp → ℤ → ℤ
  conv a b u = Σ< H (λ j → coeff a (+ j) * coeff b (u - (+ j)))

  -- The summand of a convolution is H-periodic.  (PathSum.Ring proves
  -- this too, privately.)

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


------------------------------------------------------------------------
-- Commutativity

-- Reflecting the window at u pairs a_(u-j) with b_j, which swaps the
-- factors.

⊛-comm : ∀ a b → a ⊛ b ≐ b ⊛ a
⊛-comm a b i = go (+ toℕ i)
  where
  back : ∀ u x → x ≡ u - (u - x)
  back = solve 2 (λ u x → x := u :- (u :- x)) refl

  go : ∀ u → conv a b u ≡ conv b a u
  go u = trans (Σ<-cong H term) (Σ<-reflect g (per-conv b a u) u)
    where
    g : ℤ → ℤ
    g t = coeff b t * coeff a (u - t)

    term : ∀ j → coeff a (+ j) * coeff b (u - (+ j)) ≡ g (u - (+ j))
    term j = trans (*-comm (coeff a (+ j)) (coeff b (u - (+ j))))
      (cong (coeff b (u - (+ j)) *_)
            (coeff-exp a (+ j) (u - (u - (+ j))) (back u (+ j))))

⊛-identityʳ : ∀ a → a ⊛ zpow 0ℤ ≐ a
⊛-identityʳ a i = trans (⊛-comm a (zpow 0ℤ) i) (⊛-identityˡ a i)


------------------------------------------------------------------------
-- Associativity

-- Expanding both products gives a double sum; exchanging the two sums
-- and moving the inner window by j turns one into the other.

⊛-assoc : ∀ a b c → (a ⊛ b) ⊛ c ≐ a ⊛ (b ⊛ c)
⊛-assoc a b c i = go (+ toℕ i)
  where
  shape : ∀ u x y → u - x ≡ (u - y) - (x - y)
  shape = solve 3 (λ u x y → u :- x := (u :- y) :- (x :- y)) refl

  -- The inner sum over l, its window moved by j, is a coefficient of
  -- b ⊛ c.

  moved : ∀ u j →
          Σ< H (λ l → coeff b ((+ l) - (+ j)) * coeff c (u - (+ l))) ≡
          coeff (b ⊛ c) (u - (+ j))
  moved u j = trans
    (Σ<-cong H (λ l → cong (coeff b ((+ l) - (+ j)) *_)
      (coeff-exp c (u - (+ l)) ((u - (+ j)) - ((+ l) - (+ j)))
                   (shape u (+ l) (+ j)))))
    (trans (Window.rotate g (per-conv b c (u - (+ j))) (+ j))
           (sym (coeff-⊛ b c (u - (+ j)))))
    where
    g : ℤ → ℤ
    g t = coeff b t * coeff c ((u - (+ j)) - t)

  go : ∀ u → conv (a ⊛ b) c u ≡ conv a (b ⊛ c) u
  go u = trans (Σ<-cong H expand)
    (trans (Σ<-swap H H F)
      (Σ<-cong H (λ j → trans
        (Σ<-* H (coeff a (+ j))
              (λ l → coeff b ((+ l) - (+ j)) * coeff c (u - (+ l))))
        (cong (coeff a (+ j) *_) (moved u j)))))
    where
    F : ℕ → ℕ → ℤ
    F l j = coeff a (+ j) * (coeff b ((+ l) - (+ j)) * coeff c (u - (+ l)))

    expand : ∀ l → coeff (a ⊛ b) (+ l) * coeff c (u - (+ l)) ≡
                   Σ< H (λ j → F l j)
    expand l = trans (cong (_* coeff c (u - (+ l))) (coeff-⊛ a b (+ l)))
      (trans (Σ<-*ʳ H (λ j → coeff a (+ j) * coeff b ((+ l) - (+ j)))
                      (coeff c (u - (+ l))))
             (Σ<-cong H (λ j → *-assoc (coeff a (+ j))
                                       (coeff b ((+ l) - (+ j)))
                                       (coeff c (u - (+ l))))))


------------------------------------------------------------------------
-- Conjugation is multiplicative

-- Read at -u, the convolution pairs a_j with b_(-u-j); reflecting the
-- window at 0 pairs a_(-j) with b_(j-u), which are the coefficients of
-- ā at j and of b̄ at u - j.

conj-⊛ : ∀ a b → conj (a ⊛ b) ≐ conj a ⊛ conj b
conj-⊛ a b i = go (+ toℕ i)
  where
  shape₁ : ∀ x → 0ℤ - x ≡ - x
  shape₁ = solve 1 (λ x → con 0ℤ :- x := :- x) refl

  shape₂ : ∀ u x → (- u) - (0ℤ - x) ≡ - (u - x)
  shape₂ = solve 2 (λ u x → (:- u) :- (con 0ℤ :- x) := :- (u :- x)) refl

  go : ∀ u → coeff (a ⊛ b) (- u) ≡ conv (conj a) (conj b) u
  go u = trans (coeff-⊛ a b (- u))
    (trans (sym (Σ<-reflect g (per-conv a b (- u)) 0ℤ))
           (Σ<-cong H term))
    where
    g : ℤ → ℤ
    g t = coeff a t * coeff b ((- u) - t)

    term : ∀ j → g (0ℤ - (+ j)) ≡
                 coeff (conj a) (+ j) * coeff (conj b) (u - (+ j))
    term j = cong₂ _*_
      (trans (coeff-exp a (0ℤ - (+ j)) (- (+ j)) (shape₁ (+ j)))
             (sym (coeff-conj a (+ j))))
      (trans (coeff-exp b ((- u) - (0ℤ - (+ j))) (- (u - (+ j)))
                          (shape₂ u (+ j)))
             (sym (coeff-conj b (u - (+ j)))))

-- ζ^0 is real, and conj, being an involution, is injective.

conj-1 : conj (zpow 0ℤ) ≐ zpow 0ℤ
conj-1 i = conj-zpow 0ℤ i

conj-injective : ∀ {a b} → conj a ≐ conj b → a ≐ b
conj-injective {a} {b} eq i =
  trans (sym (conj-involutive a i))
        (trans (conj-cong eq i) (conj-involutive b i))


------------------------------------------------------------------------
-- Sums over assignments

-- The recursive sum Σᴮ that amp is built from: ⊛ distributes over it
-- on either side, and conj commutes with it, one bit at a time.

Σᴮ-⊛ : ∀ {k} (f : (Fin k → Bool) → Amp) b → Σᴮ f ⊛ b ≐ Σᴮ (λ y → f y ⊛ b)
Σᴮ-⊛ {zero}  f b i = refl
Σᴮ-⊛ {suc k} f b i = trans
  (⊛-distribʳ-+ᴬ (Σᴮ (λ y → f (extend true y)))
                 (Σᴮ (λ y → f (extend false y))) b i)
  (cong₂ _+_ (Σᴮ-⊛ (λ y → f (extend true y)) b i)
             (Σᴮ-⊛ (λ y → f (extend false y)) b i))

⊛-Σᴮ : ∀ {k} a (f : (Fin k → Bool) → Amp) → a ⊛ Σᴮ f ≐ Σᴮ (λ y → a ⊛ f y)
⊛-Σᴮ {zero}  a f i = refl
⊛-Σᴮ {suc k} a f i = trans
  (⊛-distribˡ-+ᴬ a (Σᴮ (λ y → f (extend true y)))
                   (Σᴮ (λ y → f (extend false y))) i)
  (cong₂ _+_ (⊛-Σᴮ a (λ y → f (extend true y)) i)
             (⊛-Σᴮ a (λ y → f (extend false y)) i))

conj-Σᴮ : ∀ {k} (f : (Fin k → Bool) → Amp) →
          conj (Σᴮ f) ≐ Σᴮ (λ y → conj (f y))
conj-Σᴮ {zero}  f i = refl
conj-Σᴮ {suc k} f i = trans
  (conj-+ᴬ (Σᴮ (λ y → f (extend true y)))
           (Σᴮ (λ y → f (extend false y))) i)
  (cong₂ _+_ (conj-Σᴮ (λ y → f (extend true y)) i)
             (conj-Σᴮ (λ y → f (extend false y)) i))

-- The opaque integer sum Σᶻ that Σᵃ is built from commutes with a
-- window sum, so ⊛ distributes over Σᵃ as well.

Σ<-Σᶻ : ∀ {k} l (F : ℕ → (Fin k → Bool) → ℤ) →
        Σ< l (λ j → Σᶻ (λ z → F j z)) ≡ Σᶻ (λ z → Σ< l (λ j → F j z))
Σ<-Σᶻ {k} zero    F = sym (Σᶻ-0 {k})
Σ<-Σᶻ {k} (suc l) F =
  trans (cong (_+ Σᶻ (λ z → F l z)) (Σ<-Σᶻ l F))
        (sym (Σᶻ-+ (λ z → Σ< l (λ j → F j z)) (λ z → F l z)))

Σᵃ-⊛ : ∀ {k} (f : (Fin k → Bool) → Amp) b → Σᵃ f ⊛ b ≐ Σᵃ (λ z → f z ⊛ b)
Σᵃ-⊛ {k} f b i = go (+ toℕ i)
  where
  go : ∀ u → conv (Σᵃ f) b u ≡ Σᶻ (λ z → conv (f z) b u)
  go u = trans (Σ<-cong H term)
    (Σ<-Σᶻ H (λ j z → coeff (f z) (+ j) * coeff b (u - (+ j))))
    where
    term : ∀ j → coeff (Σᵃ f) (+ j) * coeff b (u - (+ j)) ≡
                 Σᶻ (λ z → coeff (f z) (+ j) * coeff b (u - (+ j)))
    term j = trans (cong (_* coeff b (u - (+ j))) (coeff-Σᵃ f (+ j)))
      (trans (*-comm (Σᶻ (λ z → coeff (f z) (+ j))) (coeff b (u - (+ j))))
        (trans (sym (Σᶻ-* (coeff b (u - (+ j))) (λ z → coeff (f z) (+ j))))
               (Σᶻ-cong (λ z → *-comm (coeff b (u - (+ j)))
                                      (coeff (f z) (+ j))))))

⊛-Σᵃ : ∀ {k} a (f : (Fin k → Bool) → Amp) → a ⊛ Σᵃ f ≐ Σᵃ (λ z → a ⊛ f z)
⊛-Σᵃ a f i = trans (⊛-comm a (Σᵃ f) i)
  (trans (Σᵃ-⊛ f a i) (Σᵃ-cong (λ z → ⊛-comm (f z) a) i))


------------------------------------------------------------------------
-- Normalisations

-- √2^j passes through a product on either side, and through conj, √2
-- being real.

scale-⊛ˡ : ∀ j a b → scale j a ⊛ b ≐ scale j (a ⊛ b)
scale-⊛ˡ zero    a b i = refl
scale-⊛ˡ (suc j) a b i =
  trans (√2·-⊛ˡ (scale j a) b i) (√2·-map (scale-⊛ˡ j a b) i)

scale-⊛ʳ : ∀ j a b → a ⊛ scale j b ≐ scale j (a ⊛ b)
scale-⊛ʳ zero    a b i = refl
scale-⊛ʳ (suc j) a b i =
  trans (√2·-⊛ʳ a (scale j b) i) (√2·-map (scale-⊛ʳ j a b) i)

conj-scale : ∀ j a → conj (scale j a) ≐ scale j (conj a)
conj-scale zero    a i = refl
conj-scale (suc j) a i =
  trans (conj-√2 (scale j a) i) (√2·-map (conj-scale j a) i)


------------------------------------------------------------------------
-- The additive group

-- Equality of amplitudes is an equivalence, and addition is the
-- pointwise addition of integers.

≐-refl : ∀ {a} → a ≐ a
≐-refl _ = refl

≐-sym : ∀ {a b} → a ≐ b → b ≐ a
≐-sym a≐b i = sym (a≐b i)

≐-trans : ∀ {a b c} → a ≐ b → b ≐ c → a ≐ c
≐-trans a≐b b≐c i = trans (a≐b i) (b≐c i)

≐-isEquivalence : IsEquivalence _≐_
≐-isEquivalence = record { refl = ≐-refl ; sym = ≐-sym ; trans = ≐-trans }

+ᴬ-cong : ∀ {a a′ b b′} → a ≐ a′ → b ≐ b′ → a +ᴬ b ≐ a′ +ᴬ b′
+ᴬ-cong a≐a′ b≐b′ i = cong₂ _+_ (a≐a′ i) (b≐b′ i)

+ᴬ-assoc : ∀ a b c → (a +ᴬ b) +ᴬ c ≐ a +ᴬ (b +ᴬ c)
+ᴬ-assoc a b c i = +-assoc (a i) (b i) (c i)

+ᴬ-identityˡ : ∀ a → 0ᴬ +ᴬ a ≐ a
+ᴬ-identityˡ a i = +-identityˡ (a i)

+ᴬ-identityʳ : ∀ a → a +ᴬ 0ᴬ ≐ a
+ᴬ-identityʳ a i = +-identityʳ (a i)

-ᴬ-cong : ∀ {a b} → a ≐ b → -ᴬ a ≐ -ᴬ b
-ᴬ-cong a≐b i = cong -_ (a≐b i)

-ᴬ-inverseˡ : ∀ a → -ᴬ a +ᴬ a ≐ 0ᴬ
-ᴬ-inverseˡ a i = +-inverseˡ (a i)

-ᴬ-inverseʳ : ∀ a → a +ᴬ -ᴬ a ≐ 0ᴬ
-ᴬ-inverseʳ a i = +-inverseʳ (a i)


------------------------------------------------------------------------
-- Z[ζ] as a commutative ring with involution

-- The standard library's commutative ring, up to ≐.

⊛-isCommutativeRing : IsCommutativeRing _≐_ _+ᴬ_ _⊛_ -ᴬ_ 0ᴬ (zpow 0ℤ)
⊛-isCommutativeRing = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = ≐-isEquivalence
              ; ∙-cong        = +ᴬ-cong
              }
            ; assoc = +ᴬ-assoc
            }
          ; identity = +ᴬ-identityˡ , +ᴬ-identityʳ
          }
        ; inverse = -ᴬ-inverseˡ , -ᴬ-inverseʳ
        ; ⁻¹-cong = -ᴬ-cong
        }
      ; comm = +ᴬ-comm
      }
    ; *-cong     = ⊛-cong
    ; *-assoc    = ⊛-assoc
    ; *-identity = ⊛-identityˡ , ⊛-identityʳ
    ; distrib    = ⊛-distribˡ-+ᴬ , (λ a b c → ⊛-distribʳ-+ᴬ b c a)
    }
  ; *-comm = ⊛-comm
  }

ℤ[ζ] : CommutativeRing 0ℓ 0ℓ
ℤ[ζ] = record { isCommutativeRing = ⊛-isCommutativeRing }

open RingMorphisms (CommutativeRing.rawRing ℤ[ζ])
                   (CommutativeRing.rawRing ℤ[ζ])
  using (IsRingHomomorphism; IsRingIsomorphism)

-- Conjugation is a ring automorphism of Z[ζ], and an involution
-- (conj-involutive): Z[ζ] is a commutative ring with involution.

conj-isRingHomomorphism : IsRingHomomorphism conj
conj-isRingHomomorphism = record
  { isSemiringHomomorphism = record
    { isNearSemiringHomomorphism = record
      { +-isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = conj-cong }
          ; homo              = conj-+ᴬ
          }
        ; ε-homo = conj-0ᴬ
        }
      ; *-homo = conj-⊛
      }
    ; 1#-homo = conj-1
    }
  ; -‿homo = conj-neg
  }

conj-isRingIsomorphism : IsRingIsomorphism conj
conj-isRingIsomorphism = record
  { isRingMonomorphism = record
    { isRingHomomorphism = conj-isRingHomomorphism
    ; injective          = conj-injective
    }
  ; surjective = λ a → conj a , λ z≐ → ≐-trans (conj-cong z≐)
                                               (conj-involutive a)
  }
