------------------------------------------------------------------------
-- Presentations of groups
--
-- Deciding whether a path-sum without path variables is the identity
--
-- Corollary 4.4 reduces a Clifford circuit's restricted path-sum until
-- no path variable is left, and PathSum.Identity supplies a criterion
-- and three refutations for what remains.  The criterion there, id-if,
-- asks for congruences between polynomials, coefficient by
-- coefficient, while the refutations each fail at a single input, so
-- they do not visibly cover every case.
--
-- This module characterises the identity input by input instead.  A
-- path-sum with no path variables has a single path, so at each input
-- x its diagonal entry is ζ^P(x) if that path returns x and 0 if not,
-- and its off-diagonal entries vanish as soon as it does return x.  So
-- it is the identity exactly when it spends no normalisation and, at
-- every x, its path returns x with P(x) ≡ 0 modulo 2^M: id-if′ is the
-- sufficiency, and the refutations give the necessity (id⇔′).  There
-- are finitely many inputs, so the question is decidable
-- (decide-≋-id) -- an elementary fact, since the matrix has finitely
-- many entries anyway.  PathSum.Syntactic turns the input-by-input
-- characterisation into the coefficient-wise one with Möbius
-- inversion.  Nothing here is polynomial-time: the search visits all
-- 2^n inputs, and evaluating a polynomial sums over all its monomials.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Decide (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (0ℤ)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using (+-identityʳ)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×?_)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Assign using (same; same-intro)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; 0ᴬ; zpow; zpow-cong)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; hits-elim; hits-≗³)
open import PathSum.Identity M₀ using
  (not-id-out; not-id-norm; not-id-phase)
open import PathSum.Isometry M₀ using (≋-id-intro)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Properties using (eval-cong)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- The single path

-- With no path variables every sum over paths has one term, so an
-- amplitude is its path's contribution or nothing.  y∅ names the one
-- path; every other path is pointwise equal to it, vacuously.

private
  y∅ : Assign 0
  y∅ ()

  if-true : {b : Bool} {a : Amp} → b ≡ true → (if b then a else 0ᴬ) ≐ a
  if-true refl _ = refl

  if-false : {b : Bool} {a : Amp} → b ≡ false → (if b then a else 0ᴬ) ≐ 0ᴬ
  if-false refl _ = refl

  ¬true : ∀ {b} → ¬ (b ≡ true) → b ≡ false
  ¬true {true}  ¬t = contradiction refl ¬t
  ¬true {false} _  = refl

  -- Moving a statement about one path to any other.

  at-y : (ξ : PathSum n k 0) (x z : Assign n) (y : Assign 0) →
         hits ξ x y∅ z ≡ hits ξ x y z
  at-y ξ x z y = hits-≗³ ξ {x} {x} {y∅} {y} {z} {z}
                   (λ _ → refl) (λ ()) (λ _ → refl)

  -- The same for the value of the phase.

  eval-at-y : (ξ : PathSum n k 0) (x : Assign n) (y : Assign 0) →
              eval (phase ξ) x y∅ ≡ eval (phase ξ) x y
  eval-at-y ξ x y =
    eval-cong (phase ξ) {x} {x} {y∅} {y} (λ _ → refl) (λ ())


------------------------------------------------------------------------
-- The criterion, input by input

-- At no normalisation, a path-sum whose single path returns every
-- input, with a phase that vanishes modulo 2^M at every input, is the
-- identity: its diagonal entries are ζ^0, and its path, returning x,
-- hits nothing else.

id-if′ : (ξ : PathSum n 0 0) →
         (∀ x y → hits ξ x y x ≡ true) →
         (∀ x y → pow M ∣ eval (phase ξ) x y) →
         ξ ≋ idPS
id-if′ ξ hit div = ≋-id-intro ξ diag off
  where
  diag : ∀ x → amp ξ x x ≐ zpow 0ℤ
  diag x i = trans (if-true (hit x y∅) i)
    (zpow-cong {eval (phase ξ) x y∅} {0ℤ}
       (subst (pow M ∣_) (sym (+-identityʳ (eval (phase ξ) x y∅)))
              (div x y∅)) i)

  off : ∀ x z → same x z ≡ false → amp ξ x z ≐ 0ᴬ
  off x z ne = if-false (¬true λ h → contradiction
    (trans (sym (same-intro x z (λ w →
              trans (sym (hits-elim ξ x y∅ x (hit x y∅) w))
                    (hits-elim ξ x y∅ z h w))))
           ne)
    λ ())


------------------------------------------------------------------------
-- Searching every input

-- A decidable property that reads an assignment only through its
-- values either holds everywhere or fails somewhere, and the search
-- says which, with a witness.

private
  cons-≗ : ∀ b {g g′ : Fin n → Bool} → (∀ i → g i ≡ g′ i) →
           ∀ i → (b ∷ᵃ g) i ≡ (b ∷ᵃ g′) i
  cons-≗ b g≗ zero    = refl
  cons-≗ b g≗ (suc i) = g≗ i

  split : (x : Fin (suc n) → Bool) →
          ∀ i → (x zero ∷ᵃ (λ j → x (suc j))) i ≡ x i
  split x zero    = refl
  split x (suc i) = refl

search : (P : (Fin n → Bool) → Set) → (∀ x → Dec (P x)) →
         (∀ {x x′} → (∀ i → x i ≡ x′ i) → P x → P x′) →
         (∀ x → P x) ⊎ ∃ (λ x → ¬ P x)
search {zero} P P? resp with P? y∅
... | yes p = inj₁ (λ x → resp (λ ()) p)
... | no ¬p = inj₂ (y∅ , ¬p)
search {suc n} P P? resp
  with search (λ g → P (false ∷ᵃ g)) (λ g → P? (false ∷ᵃ g))
              (λ g≗ → resp (cons-≗ false g≗))
     | search (λ g → P (true ∷ᵃ g)) (λ g → P? (true ∷ᵃ g))
              (λ g≗ → resp (cons-≗ true g≗))
... | inj₂ (g , ¬p) | _             = inj₂ (false ∷ᵃ g , ¬p)
... | inj₁ _        | inj₂ (g , ¬p) = inj₂ (true ∷ᵃ g , ¬p)
... | inj₁ all₀     | inj₁ all₁     = inj₁ (λ x →
  resp (split x) (pick (x zero) (λ j → x (suc j))))
  where
  pick : ∀ b g → P (b ∷ᵃ g)
  pick false g = all₀ g
  pick true  g = all₁ g


------------------------------------------------------------------------
-- The decision

-- What id-if′ asks of one input.

private
  Good : PathSum n k 0 → (Fin n → Bool) → Set
  Good ξ x = (hits ξ x y∅ x ≡ true) × (pow M ∣ eval (phase ξ) x y∅)

  good? : (ξ : PathSum n k 0) → ∀ x → Dec (Good ξ x)
  good? ξ x = (hits ξ x y∅ x ≟ᵇ true) ×? (pow M ∣? eval (phase ξ) x y∅)

  good-≗ : (ξ : PathSum n k 0) → ∀ {x x′} → (∀ i → x i ≡ x′ i) →
           Good ξ x → Good ξ x′
  good-≗ ξ {x} {x′} x≗x′ (h , d) =
    trans (sym (hits-≗³ ξ {x} {x′} {y∅} {y∅} {x} {x′} x≗x′ (λ ()) x≗x′)) h ,
    subst (pow M ∣_)
          (eval-cong (phase ξ) {x} {x′} {y∅} {y∅} x≗x′ (λ ())) d

  x₀ : Fin n → Bool
  x₀ _ = false

-- A path-sum with no path variables is the identity or it is not, and
-- which is decided input by input.  Spending no normalisation is
-- necessary -- at x₀ the path either returns, and not-id-norm applies,
-- or it does not, and not-id-out does -- and at no normalisation an
-- input failing the criterion is refuted by not-id-out or
-- not-id-phase.

-- (The case splits go through helpers that take a Boolean together
-- with its equation, rather than `with`: abstracting over a goal that
-- mentions ≋ makes Agda unfold amp, and costs gigabytes.)

private
  -- Some normalisation left: refuted at x₀ either way.
  spent : (ξ : PathSum n (suc k) 0) →
          ∀ b → hits ξ x₀ y∅ x₀ ≡ b → ¬ (ξ ≋ idPS)
  spent ξ true  eq = not-id-norm ξ x₀ y∅ eq
  spent ξ false eq = not-id-out ξ x₀ (λ y → trans (sym (at-y ξ x₀ x₀ y)) eq)

  -- No normalisation, and an input x fails the criterion.
  fails : (ξ : PathSum n 0 0) (x : Fin n → Bool) → ¬ Good ξ x →
          ∀ b → hits ξ x y∅ x ≡ b → ¬ (ξ ≋ idPS)
  fails ξ x bad false eq =
    not-id-out ξ x (λ y → trans (sym (at-y ξ x x y)) eq)
  fails ξ x bad true  eq = not-id-phase ξ x y∅ eq (λ d → bad (eq , d))

  -- No normalisation: the search decides.
  settle : (ξ : PathSum n 0 0) →
           (∀ x → Good ξ x) ⊎ ∃ (λ x → ¬ Good ξ x) → Dec (ξ ≋ idPS)
  settle ξ (inj₁ good) = yes (id-if′ ξ
    (λ x y → trans (sym (at-y ξ x x y)) (proj₁ (good x)))
    (λ x y → subst (pow M ∣_) (eval-at-y ξ x y) (proj₂ (good x))))
  settle ξ (inj₂ (x , bad)) = no (fails ξ x bad (hits ξ x y∅ x) refl)

decide-≋-id : (ξ : PathSum n k 0) → Dec (ξ ≋ idPS)
decide-≋-id {k = suc k} ξ = no (spent ξ (hits ξ x₀ y∅ x₀) refl)
decide-≋-id {k = zero}  ξ = settle ξ (search (Good ξ) (good? ξ) (good-≗ ξ))


------------------------------------------------------------------------
-- The criterion is also necessary

-- The refutations are the other half of id-if′: the identity spends no
-- normalisation, and at every input its path returns the input with a
-- phase that vanishes modulo 2^M.

id-no-norm : (ξ : PathSum n (suc k) 0) → ¬ (ξ ≋ idPS)
id-no-norm ξ = spent ξ (hits ξ x₀ y∅ x₀) refl

private
  good-of-id : (ξ : PathSum n 0 0) → ξ ≋ idPS →
               ∀ x → Dec (Good ξ x) → Good ξ x
  good-of-id ξ ξ≋id x (yes g)   = g
  good-of-id ξ ξ≋id x (no  bad) =
    contradiction ξ≋id (fails ξ x bad (hits ξ x y∅ x) refl)

id-only-if′ : (ξ : PathSum n 0 0) → ξ ≋ idPS →
              (∀ x y → hits ξ x y x ≡ true) ×
              (∀ x y → pow M ∣ eval (phase ξ) x y)
id-only-if′ ξ ξ≋id =
  (λ x y → trans (sym (at-y ξ x x y)) (proj₁ (good x))) ,
  (λ x y → subst (pow M ∣_) (eval-at-y ξ x y) (proj₂ (good x)))
  where
  good : ∀ x → Good ξ x
  good x = good-of-id ξ ξ≋id x (good? ξ x)

id⇔′ : (ξ : PathSum n 0 0) →
       (ξ ≋ idPS ⇔
        ((∀ x y → hits ξ x y x ≡ true) ×
         (∀ x y → pow M ∣ eval (phase ξ) x y)))
id⇔′ ξ = mk⇔ (id-only-if′ ξ) (λ (h , d) → id-if′ ξ h d)
