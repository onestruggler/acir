------------------------------------------------------------------------
-- Presentations of groups
--
-- Fourier (parity) expansions of phase polynomials (Amy, QPL 2018,
-- section 2.2)
--
-- Section 2.2 of the paper notes that "the phase polynomial could
-- instead be represented ... by its Fourier expansion [1, 26]", and
-- that "the Fourier expansion is not necessarily unique modulo integer
-- multiples".  A Fourier expansion writes a phase as a sum of
-- coefficients times parities,
--
--    c + Σ_i a_i · [⨁_{v ∈ S_i} v] ,
--
-- the parity [⨁ S] of a set S of input and path variables read as 0
-- or 1 (PathSum.Linear.parᵐ).  Here an expansion is a constant and a
-- list of terms (a , S) with integer numerators (Expansion), its value
-- at a point is valueᶠ, and its coefficient on a parity set the sum of
-- the numerators of the terms listing that set (coefᶠ).
--
-- * Every phase polynomial has one (expand-value).  The multilinear
--   x^γ is not a combination of parities with numerators over the same
--   power of two -- x1x2x3/8 needs a coefficient 1/32 -- so the
--   expansion is stated at a raised precision: for P : Poly n m, the
--   expansion expandᴾ P has value exactly 2^(n+m) · P at every point,
--   i.e. it represents P/2^M with numerators over 2^(M+n+m)
--   (FourierOf, expand-fourier).  The construction is Shannon's: on a
--   new variable b, f = f₀ + [b](f₁ − f₀), and 2[b]·[S] is
--   [b] + [S] − [b ⊕ S] (combine).  It is exponential in the number
--   of variables, as it must be for an arbitrary polynomial.  The
--   paper's point, that the phase of a circuit has an expansion of
--   size linear in the circuit -- a parity per R_k, three per
--   Hadamard, and no raised precision -- is PathSum.Fourier.Circuit.
--
-- * Expansions are not unique modulo 1 (Examples.Fourier): two
--   expansions whose coefficients differ modulo 1 can have the same
--   value modulo 1 at every point.
--
-- * The multilinear form, by contrast, is unique modulo 1: two phase
--   polynomials with the same values modulo 1 at every point have the
--   same coefficients modulo 1 (phase-unique, Möbius inversion through
--   PathSum.Polynomial.Boolean.≈-from-values).  So a representation of
--   a path-sum's phase by its multilinear coefficients reads them off
--   uniquely, which is what PathSum.Size.Cubic's lower bound uses.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Fourier (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Subset using (Subset; inside; outside; ⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; ⌊_⌋)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Compose.Sum M₀ using (_++ᵃ_; ++ᵃ-↑ˡ; ++ᵃ-↑ʳ)
open import PathSum.Cyclotomic M₀ using (extend)
open import PathSum.Linear using (par; parᵐ; par-⊥; par-cong)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using (Poly; Mon; _≟ᵐ_; eval; _≈[_]_)
open import PathSum.Polynomial.Boolean using (≈-from-values)
open import PathSum.Polynomial.Decidable using (all-points?)
open import PathSum.Polynomial.Properties using (eval-cong; i∣0)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- Expansions

-- A constant and a list of terms a · [⨁ S].

Expansion : ℕ → ℕ → Set
Expansion n m = ℤ × List (ℤ × Mon n m)

Σᶠ : List (ℤ × Mon n m) → (Fin n → Bool) → (Fin m → Bool) → ℤ
Σᶠ []             x y = 0ℤ
Σᶠ ((a , S) ∷ ts) x y = a * [ parᵐ S x y ]ᶻ + Σᶠ ts x y

valueᶠ : Expansion n m → (Fin n → Bool) → (Fin m → Bool) → ℤ
valueᶠ (c , ts) x y = c + Σᶠ ts x y

-- The number of terms.

sizeᶠ : Expansion n m → ℕ
sizeᶠ (_ , ts) = length ts

-- The coefficient on a parity set: the terms listing it, summed.

coefᶠ : Expansion n m → Mon n m → ℤ
coefᶠ (_ , ts) γ = go ts
  where
  go : List (ℤ × Mon _ _) → ℤ
  go []             = 0ℤ
  go ((a , S) ∷ ts) = (if ⌊ S ≟ᵐ γ ⌋ then a else 0ℤ) + go ts

-- E represents the phase P/2^M with numerators over 2^(M+e): their
-- values agree modulo 1 at every point.

FourierOf : ℕ → Expansion n m → Poly n m → Set
FourierOf {n} {m} e E P =
  ∀ (x : Fin n → Bool) (y : Fin m → Bool) →
  pow (M ℕ+ e) ∣ (valueᶠ E x y - pow e * eval P x y)


------------------------------------------------------------------------
-- Expansions over one block of variables

-- Over k variables, with parity sets Subset k.

private
  Termsᵏ : ℕ → Set
  Termsᵏ k = List (ℤ × Subset k)

  Σᵏ : Termsᵏ k → (Fin k → Bool) → ℤ
  Σᵏ []             z = 0ℤ
  Σᵏ ((a , S) ∷ ts) z = a * [ par S z ]ᶻ + Σᵏ ts z

  valueᵏ : ℤ × Termsᵏ k → (Fin k → Bool) → ℤ
  valueᵏ (c , ts) z = c + Σᵏ ts z

  -- A new variable y₀ in front: the old sets without it, and with it.

  wkS addS : Subset k → Subset (suc k)
  wkS S  = outside ∷ S
  addS S = inside ∷ S

  y₀S : Subset (suc k)
  y₀S = inside ∷ ⊥

  dbl : ℤ × Subset k → ℤ × Subset (suc k)
  dbl (a , S) = (+ 2) * a , wkS S

  -- 2[y₀]·a[S] = a[y₀] + a[S] − a[y₀ ⊕ S].

  triple : ℤ × Subset k → Termsᵏ (suc k)
  triple (a , S) = (a , y₀S) ∷ (a , wkS S) ∷ (- a , addS S) ∷ []

  triples : Termsᵏ k → Termsᵏ (suc k)
  triples []       = []
  triples (t ∷ ts) = triple t ++ triples ts

  -- f = f₀ + [y₀](f₁ − f₀), doubled.

  combine : ℤ × Termsᵏ k → ℤ × Termsᵏ k → ℤ × Termsᵏ (suc k)
  combine (c₀ , t₀) (c₁ , t₁) =
    (+ 2) * c₀ , map dbl t₀ ++ ((+ 2) * c₁ , y₀S) ∷ triples t₁

  -- Its value, read at b and the rest g.

  Σᵏ-++ : (ts us : Termsᵏ k) (z : Fin k → Bool) →
          Σᵏ (ts ++ us) z ≡ Σᵏ ts z + Σᵏ us z
  Σᵏ-++ []             us z = sym (solve 1 (λ u → con 0ℤ :+ u := u) refl _)
  Σᵏ-++ ((a , S) ∷ ts) us z = trans
    (cong (λ t → a * [ par S z ]ᶻ + t) (Σᵏ-++ ts us z))
    (solve 3 (λ p s u → p :+ (s :+ u) := (p :+ s) :+ u) refl
           (a * [ par S z ]ᶻ) (Σᵏ ts z) (Σᵏ us z))

  Σᵏ-dbl : (ts : Termsᵏ k) (b : Bool) (g : Fin k → Bool) →
           Σᵏ (map dbl ts) (extend b g) ≡ (+ 2) * Σᵏ ts g
  Σᵏ-dbl []             b g = refl
  Σᵏ-dbl ((a , S) ∷ ts) b g = trans
    (cong₂ (λ p q → (+ 2) * a * [ p ]ᶻ + q)
           (par-cong S {f = λ i → extend b g (suc i)} {g = g} (λ _ → refl))
           (Σᵏ-dbl ts b g))
    (solve 3 (λ a p s → con (+ 2) :* a :* p :+ con (+ 2) :* s :=
                        con (+ 2) :* (a :* p :+ s))
           refl a [ par S g ]ᶻ (Σᵏ ts g))

  bit-y₀ : ∀ (b : Bool) (g : Fin k → Bool) → par y₀S (extend b g) ≡ b
  bit-y₀ b g = trans (cong (b xor_) (par-⊥ g)) (xor-identityʳ b)

  -- [b] + [s] − [b ⊕ s] = 2[b][s].

  xor-bits : ∀ b s → [ b ]ᶻ + [ s ]ᶻ - [ b xor s ]ᶻ ≡ (+ 2) * ([ b ]ᶻ * [ s ]ᶻ)
  xor-bits false false = refl
  xor-bits false true  = refl
  xor-bits true  false = refl
  xor-bits true  true  = refl

  Σᵏ-triples : (ts : Termsᵏ k) (b : Bool) (g : Fin k → Bool) →
               Σᵏ (triples ts) (extend b g) ≡ (+ 2) * [ b ]ᶻ * Σᵏ ts g
  Σᵏ-triples []             b g = sym (solve 1 (λ t → t :* con 0ℤ := con 0ℤ)
                                              refl ((+ 2) * [ b ]ᶻ))
  Σᵏ-triples ((a , S) ∷ ts) b g = trans
    (cong₂ (λ p q → a * [ p ]ᶻ + (a * [ s ]ᶻ + (- a * [ b xor s ]ᶻ + q)))
           (bit-y₀ b g) (Σᵏ-triples ts b g))
    (trans (shape a [ b ]ᶻ [ s ]ᶻ [ b xor s ]ᶻ (Σᵏ ts g))
      (trans (cong (λ t → a * t + (+ 2) * [ b ]ᶻ * Σᵏ ts g) (xor-bits b s))
             (final a [ b ]ᶻ [ s ]ᶻ (Σᵏ ts g))))
    where
    s : Bool
    s = par S g

    shape : ∀ a p q r σ →
            a * p + (a * q + (- a * r + (+ 2) * p * σ)) ≡
            a * (p + q - r) + (+ 2) * p * σ
    shape = solve 5 (λ a p q r σ →
      a :* p :+ (a :* q :+ ((:- a) :* r :+ con (+ 2) :* p :* σ)) :=
      a :* (p :+ q :- r) :+ con (+ 2) :* p :* σ) refl

    final : ∀ a p q σ →
            a * ((+ 2) * (p * q)) + (+ 2) * p * σ ≡ (+ 2) * p * (a * q + σ)
    final = solve 4 (λ a p q σ →
      a :* (con (+ 2) :* (p :* q)) :+ con (+ 2) :* p :* σ :=
      con (+ 2) :* p :* (a :* q :+ σ)) refl

  value-combine : (E₀ E₁ : ℤ × Termsᵏ k) (b : Bool) (g : Fin k → Bool) →
                  valueᵏ (combine E₀ E₁) (extend b g) ≡
                  (+ 2) * valueᵏ E₀ g + (+ 2) * [ b ]ᶻ * valueᵏ E₁ g
  value-combine (c₀ , t₀) (c₁ , t₁) b g = trans
    (cong (λ t → (+ 2) * c₀ + t)
      (trans (Σᵏ-++ (map dbl t₀) (((+ 2) * c₁ , y₀S) ∷ triples t₁) (extend b g))
             (cong₂ (λ p q → p + ((+ 2) * c₁ * [ q ]ᶻ + Σᵏ (triples t₁)
                                                          (extend b g)))
                    (Σᵏ-dbl t₀ b g) (bit-y₀ b g))))
    (trans (cong (λ q → (+ 2) * c₀ + ((+ 2) * Σᵏ t₀ g +
                                      ((+ 2) * c₁ * [ b ]ᶻ + q)))
                 (Σᵏ-triples t₁ b g))
           (shape c₀ (Σᵏ t₀ g) c₁ [ b ]ᶻ (Σᵏ t₁ g)))
    where
    shape : ∀ c₀ σ₀ c₁ p σ₁ →
            (+ 2) * c₀ + ((+ 2) * σ₀ + ((+ 2) * c₁ * p + (+ 2) * p * σ₁)) ≡
            (+ 2) * (c₀ + σ₀) + (+ 2) * p * (c₁ + σ₁)
    shape = solve 5 (λ c₀ σ₀ c₁ p σ₁ →
      con (+ 2) :* c₀ :+ (con (+ 2) :* σ₀ :+
        (con (+ 2) :* c₁ :* p :+ con (+ 2) :* p :* σ₁)) :=
      con (+ 2) :* (c₀ :+ σ₀) :+ con (+ 2) :* p :* (c₁ :+ σ₁)) refl

  -- The value reads the point through its values.

  Σᵏ-cong : (ts : Termsᵏ k) {z z′ : Fin k → Bool} → (∀ i → z i ≡ z′ i) →
            Σᵏ ts z ≡ Σᵏ ts z′
  Σᵏ-cong []             h = refl
  Σᵏ-cong ((a , S) ∷ ts) h =
    cong₂ (λ p q → a * [ p ]ᶻ + q) (par-cong S h) (Σᵏ-cong ts h)

  valueᵏ-cong : (E : ℤ × Termsᵏ k) {z z′ : Fin k → Bool} →
                (∀ i → z i ≡ z′ i) → valueᵏ E z ≡ valueᵏ E z′
  valueᵏ-cong (c , ts) h = cong (λ t → c + t) (Σᵏ-cong ts h)


------------------------------------------------------------------------
-- Every function on the cube has an expansion, at precision 2^k

-- Functions reading the point through its values.

Respects : ((Fin k → Bool) → ℤ) → Set
Respects {k} f = ∀ {z z′ : Fin k → Bool} → (∀ i → z i ≡ z′ i) → f z ≡ f z′

private
  expandᵏ : ∀ k → ((Fin k → Bool) → ℤ) → ℤ × Termsᵏ k
  expandᵏ zero    f = f (λ ()) , []
  expandᵏ (suc k) f =
    combine (expandᵏ k (λ g → f (extend false g)))
            (expandᵏ k (λ g → f (extend true g) - f (extend false g)))

  -- 2^k f, by Shannon's expansion on the first variable.

  value-expandᵏ : ∀ k (f : (Fin k → Bool) → ℤ) → Respects f →
                  ∀ z → valueᵏ (expandᵏ k f) z ≡ pow k * f z
  value-expandᵏ zero    f resp z = trans (shape (f (λ ())))
    (cong (pow 0 *_) (resp {z = λ ()} {z′ = z} (λ ())))
    where
    shape : ∀ a → a + 0ℤ ≡ pow 0 * a
    shape = solve 1 (λ a → a :+ con 0ℤ := con 1ℤ :* a) refl
  value-expandᵏ (suc k) f resp z = trans
    (valueᵏ-cong (expandᵏ (suc k) f) {z = z} {z′ = extend b g} split)
    (trans (value-combine (expandᵏ k f₀) (expandᵏ k f₁₀) b g)
      (trans (cong₂ (λ p q → (+ 2) * p + (+ 2) * [ b ]ᶻ * q)
                    (value-expandᵏ k f₀ resp₀ g)
                    (value-expandᵏ k f₁₀ resp₁₀ g))
             (finish b refl)))
    where
    b : Bool
    b = z zero

    g : Fin k → Bool
    g i = z (suc i)

    split : ∀ i → z i ≡ extend b g i
    split zero    = refl
    split (suc i) = refl

    f₀ f₁ f₁₀ : (Fin k → Bool) → ℤ
    f₀ g′  = f (extend false g′)
    f₁ g′  = f (extend true g′)
    f₁₀ g′ = f₁ g′ - f₀ g′

    ext-≗ : ∀ c {g′ g″ : Fin k → Bool} → (∀ i → g′ i ≡ g″ i) →
            ∀ i → extend c g′ i ≡ extend c g″ i
    ext-≗ c h zero    = refl
    ext-≗ c h (suc i) = h i

    resp₀ : Respects f₀
    resp₀ h = resp (ext-≗ false h)

    resp₁₀ : Respects f₁₀
    resp₁₀ h = cong₂ _-_ (resp (ext-≗ true h)) (resp (ext-≗ false h))

    -- With the first bit known.

    back : ∀ c → b ≡ c → ∀ i → extend c g i ≡ z i
    back c e i = trans (cong (λ d → extend d g i) (sym e)) (sym (split i))

    finish : ∀ c → b ≡ c →
             (+ 2) * (pow k * f₀ g) + (+ 2) * [ b ]ᶻ * (pow k * f₁₀ g) ≡
             pow (suc k) * f z
    finish false e = trans
      (cong (λ c → (+ 2) * (pow k * f₀ g) + (+ 2) * [ c ]ᶻ * (pow k * f₁₀ g)) e)
      (trans (shape₀ (pow k) (f₀ g) (f₁₀ g))
             (cong₂ _*_ (sym (pow-suc k)) (resp (back false e))))
      where
      shape₀ : ∀ p a d → (+ 2) * (p * a) + (+ 2) * 0ℤ * (p * d) ≡ p * (+ 2) * a
      shape₀ = solve 3 (λ p a d →
        con (+ 2) :* (p :* a) :+ con (+ 2) :* con 0ℤ :* (p :* d) :=
        p :* con (+ 2) :* a) refl
    finish true e = trans
      (cong (λ c → (+ 2) * (pow k * f₀ g) + (+ 2) * [ c ]ᶻ * (pow k * f₁₀ g)) e)
      (trans (shape₁ (pow k) (f₀ g) (f₁ g))
             (cong₂ _*_ (sym (pow-suc k)) (resp (back true e))))
      where
      shape₁ : ∀ p a c → (+ 2) * (p * a) + (+ 2) * 1ℤ * (p * (c - a)) ≡
                         p * (+ 2) * c
      shape₁ = solve 3 (λ p a c →
        con (+ 2) :* (p :* a) :+ con (+ 2) :* con 1ℤ :* (p :* (c :- a)) :=
        p :* con (+ 2) :* c) refl


------------------------------------------------------------------------
-- From one block to inputs and path variables

private
  -- A parity set over n + m variables as a monomial in the inputs and
  -- the path variables.

  unflat : ∀ n {m} → Subset (n ℕ+ m) → Mon n m
  unflat zero    S       = [] , S
  unflat (suc n) (s ∷ S) = s ∷ proj₁ (unflat n S) , proj₂ (unflat n S)

  parᵐ-unflat : ∀ n {m} (S : Subset (n ℕ+ m)) (x : Fin n → Bool)
                (y : Fin m → Bool) →
                parᵐ (unflat n S) x y ≡ par S (x ++ᵃ y)
  parᵐ-unflat zero    S             x y = refl
  parᵐ-unflat (suc n) (inside ∷ S)  x y = trans
    (xor-assoc (x zero) (par (proj₁ (unflat n S)) (λ i → x (suc i)))
               (par (proj₂ (unflat n S)) y))
    (cong (x zero xor_) (parᵐ-unflat n S (λ i → x (suc i)) y))
  parᵐ-unflat (suc n) (outside ∷ S) x y =
    parᵐ-unflat n S (λ i → x (suc i)) y

  liftE : ℤ × Termsᵏ (n ℕ+ m) → Expansion n m
  liftE {n} (c , ts) = c , map (λ t → proj₁ t , unflat n (proj₂ t)) ts

  Σᶠ-liftE : (ts : Termsᵏ (n ℕ+ m)) (x : Fin n → Bool) (y : Fin m → Bool) →
             Σᶠ (map (λ t → proj₁ t , unflat n (proj₂ t)) ts) x y ≡
             Σᵏ ts (x ++ᵃ y)
  Σᶠ-liftE {n} []             x y = refl
  Σᶠ-liftE {n} ((a , S) ∷ ts) x y =
    cong₂ (λ p q → a * [ p ]ᶻ + q) (parᵐ-unflat n S x y) (Σᶠ-liftE ts x y)

-- The expansion of a phase polynomial: of its values, read on the
-- inputs and path variables in one block.

expandᴾ : Poly n m → Expansion n m
expandᴾ {n} {m} P =
  liftE (expandᵏ (n ℕ+ m) (λ z → eval P (λ i → z (i ↑ˡ m)) (λ j → z (n ↑ʳ j))))

-- Its value is 2^(n+m) times P's, exactly.

expand-value : (P : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
               valueᶠ (expandᴾ P) x y ≡ pow (n ℕ+ m) * eval P x y
expand-value {n} {m} P x y = trans
  (cong (λ t → proj₁ E + t) (Σᶠ-liftE (proj₂ E) x y))
  (trans (value-expandᵏ (n ℕ+ m) f resp (x ++ᵃ y))
         (cong (pow (n ℕ+ m) *_)
               (eval-cong P (++ᵃ-↑ˡ x y) (++ᵃ-↑ʳ x y))))
  where
  f : (Fin (n ℕ+ m) → Bool) → ℤ
  f z = eval P (λ i → z (i ↑ˡ m)) (λ j → z (n ↑ʳ j))

  E : ℤ × Termsᵏ (n ℕ+ m)
  E = expandᵏ (n ℕ+ m) f

  resp : Respects f
  resp h = eval-cong P (λ i → h (i ↑ˡ m)) (λ j → h (n ↑ʳ j))

-- So every phase polynomial has a Fourier expansion, with numerators
-- over 2^(M+n+m).

expand-fourier : (P : Poly n m) → FourierOf (n ℕ+ m) (expandᴾ P) P
expand-fourier {n} {m} P x y = subst (pow (M ℕ+ (n ℕ+ m)) ∣_)
  (sym (trans (cong (λ v → v - pow (n ℕ+ m) * eval P x y) (expand-value P x y))
              (+-inverseʳ (pow (n ℕ+ m) * eval P x y))))
  i∣0


------------------------------------------------------------------------
-- Deciding that an expansion represents a phase

-- The value reads the point through its values.

Σᶠ-cong : (ts : List (ℤ × Mon n m)) {x x′ : Fin n → Bool}
          {y y′ : Fin m → Bool} → (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
          Σᶠ ts x y ≡ Σᶠ ts x′ y′
Σᶠ-cong []                   hx hy = refl
Σᶠ-cong ((a , (α , β)) ∷ ts) hx hy =
  cong₂ (λ p q → a * [ p ]ᶻ + q)
        (cong₂ _xor_ (par-cong α hx) (par-cong β hy)) (Σᶠ-cong ts hx hy)

valueᶠ-cong : (E : Expansion n m) {x x′ : Fin n → Bool}
              {y y′ : Fin m → Bool} → (∀ i → x i ≡ x′ i) →
              (∀ j → y j ≡ y′ j) → valueᶠ E x y ≡ valueᶠ E x′ y′
valueᶠ-cong (c , ts) hx hy = cong (λ t → c + t) (Σᶠ-cong ts hx hy)

-- At every point of the cube.

fourierOf? : (e : ℕ) (E : Expansion n m) (P : Poly n m) →
             Dec (FourierOf e E P)
fourierOf? e E P = all-points? resp (λ x y → pow (M ℕ+ e) ∣?
                                       (valueᶠ E x y - pow e * eval P x y))
  where
  resp : ∀ {x x′ y y′} → (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
         pow (M ℕ+ e) ∣ (valueᶠ E x y - pow e * eval P x y) →
         pow (M ℕ+ e) ∣ (valueᶠ E x′ y′ - pow e * eval P x′ y′)
  resp hx hy = subst (pow (M ℕ+ e) ∣_)
    (cong₂ (λ a b → a - pow e * b) (valueᶠ-cong E hx hy) (eval-cong P hx hy))


------------------------------------------------------------------------
-- The multilinear form is unique modulo 1

-- Phases with the same values modulo 1 have the same coefficients
-- modulo 1 (Möbius inversion).

phase-unique : (P Q : Poly n m) →
               (∀ x y → pow M ∣ (eval P x y - eval Q x y)) →
               P ≈[ pow M ] Q
phase-unique P Q = ≈-from-values P Q
