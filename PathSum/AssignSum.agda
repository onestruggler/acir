------------------------------------------------------------------------
-- Presentations of groups
--
-- Integer sums over Boolean assignments
--
-- Lemma 4.1 compares a path-sum with its restriction to the diagonal
-- by summing a norm over every output assignment z : Fin n → Bool, and
-- concludes from a vanishing sum of non-negative terms that every
-- term vanishes.  This module supplies those sums.  Σᶻ f adds f up
-- over the 2^k assignments by splitting on the head bit, as Σᴮ does
-- for amplitudes; the assignments the recursion visits are built bit
-- by bit, so they are only pointwise equal to a given one, and every
-- lemma that has to meet an arbitrary assignment asks the summand to
-- respect pointwise equality.
--
-- Besides linearity and positivity, a sum can be taken apart in two
-- ways: at one point x, the rest being summed with x masked out; and
-- at one bit i, the two values of that bit being paired up in a
-- single term, which lives on the assignments giving i false.
--
-- Σᶻ is opaque, and everything about it is derived from its two
-- defining equations.  A transparent Σᶻ {k} f is stuck until k is
-- known, so k could never be recovered from it by unification; an
-- opaque one is rigid, and a statement such as Σᶻ {k} (λ _ → 0ℤ) ≡ 0ℤ,
-- which mentions k nowhere else, can then be used without naming k.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.AssignSum where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_; _*_; _≤_)
open import Data.Integer.Properties using
  (+-assoc; +-comm; +-identityʳ; *-distribˡ-+; +-mono-≤; +-monoʳ-≤;
   ≤-antisym; ≤-reflexive; ≤-trans; +-commutativeSemigroup)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)

open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using (x∙yz≈y∙xz)

import Data.Fin.Properties as Fin

open import PathSum.Assign

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- The sum

-- An assignment to k + 1 bits is a head bit followed by an assignment
-- to the other k.

infixr 5 _∷ᵃ_

_∷ᵃ_ : Bool → (Fin k → Bool) → (Fin (ℕ.suc k) → Bool)
(b ∷ᵃ g) zero    = b
(b ∷ᵃ g) (suc j) = g j

opaque
  Σᶻ : ((Fin k → Bool) → ℤ) → ℤ
  Σᶻ {ℕ.zero}  f = f (λ ())
  Σᶻ {ℕ.suc k} f = Σᶻ (λ g → f (false ∷ᵃ g)) + Σᶻ (λ g → f (true ∷ᵃ g))

  -- The defining equations, through which the rest of the module and
  -- its clients see the sum.

  Σᶻ-zero : (f : (Fin ℕ.zero → Bool) → ℤ) → Σᶻ f ≡ f (λ ())
  Σᶻ-zero f = refl

  Σᶻ-suc : (f : (Fin (ℕ.suc k) → Bool) → ℤ) →
           Σᶻ f ≡ Σᶻ (λ g → f (false ∷ᵃ g)) + Σᶻ (λ g → f (true ∷ᵃ g))
  Σᶻ-suc f = refl

-- A summand that sees assignments only through their values.

RespectsZ : ((Fin k → Bool) → ℤ) → Set
RespectsZ f = ∀ g h → (∀ j → g j ≡ h j) → f g ≡ f h

private
  -- Every assignment is, pointwise, its head bit followed by its tail.

  ∷ᵃ-η : (z : Fin (ℕ.suc k) → Bool) →
         ∀ j → (z zero ∷ᵃ (λ i → z (suc i))) j ≡ z j
  ∷ᵃ-η z zero    = refl
  ∷ᵃ-η z (suc j) = refl

  ∷ᵃ-cong : (b : Bool) {g h : Fin k → Bool} → (∀ j → g j ≡ h j) →
            ∀ j → (b ∷ᵃ g) j ≡ (b ∷ᵃ h) j
  ∷ᵃ-cong b g≗h zero    = refl
  ∷ᵃ-cong b g≗h (suc j) = g≗h j

  -- Fixing the head bit keeps a summand respectful.

  respects-∷ᵃ : {f : (Fin (ℕ.suc k) → Bool) → ℤ} → RespectsZ f →
                ∀ b → RespectsZ (λ g → f (b ∷ᵃ g))
  respects-∷ᵃ resp b g h g≗h = resp (b ∷ᵃ g) (b ∷ᵃ h) (∷ᵃ-cong b g≗h)


------------------------------------------------------------------------
-- Linearity

-- Each is an induction on the number of bits, the two halves of a sum
-- being handled by the hypothesis.

Σᶻ-cong : {f g : (Fin k → Bool) → ℤ} → (∀ z → f z ≡ g z) → Σᶻ f ≡ Σᶻ g
Σᶻ-cong {ℕ.zero}  {f} {g} f≗g =
  trans (Σᶻ-zero f) (trans (f≗g (λ ())) (sym (Σᶻ-zero g)))
Σᶻ-cong {ℕ.suc k} {f} {g} f≗g = trans (Σᶻ-suc f) (trans
  (cong₂ _+_ (Σᶻ-cong (λ z → f≗g (false ∷ᵃ z)))
             (Σᶻ-cong (λ z → f≗g (true  ∷ᵃ z))))
  (sym (Σᶻ-suc g)))

private
  -- The four halves of two sums, regrouped.

  medial : ∀ p q r s → (p + q) + (r + s) ≡ (p + r) + (q + s)
  medial p q r s = trans (+-assoc p q (r + s))
    (trans (cong (p +_) (x∙yz≈y∙xz q r s)) (sym (+-assoc p r (q + s))))

Σᶻ-+ : (f g : (Fin k → Bool) → ℤ) →
       Σᶻ (λ z → f z + g z) ≡ Σᶻ f + Σᶻ g
Σᶻ-+ {ℕ.zero}  f g = trans (Σᶻ-zero (λ z → f z + g z))
  (sym (cong₂ _+_ (Σᶻ-zero f) (Σᶻ-zero g)))
Σᶻ-+ {ℕ.suc k} f g = begin
  Σᶻ (λ z → f z + g z)
    ≡⟨ Σᶻ-suc (λ z → f z + g z) ⟩
  Σᶻ (λ z → f₀ z + g₀ z) + Σᶻ (λ z → f₁ z + g₁ z)
    ≡⟨ cong₂ _+_ (Σᶻ-+ f₀ g₀) (Σᶻ-+ f₁ g₁) ⟩
  (Σᶻ f₀ + Σᶻ g₀) + (Σᶻ f₁ + Σᶻ g₁)
    ≡⟨ medial (Σᶻ f₀) (Σᶻ g₀) (Σᶻ f₁) (Σᶻ g₁) ⟩
  (Σᶻ f₀ + Σᶻ f₁) + (Σᶻ g₀ + Σᶻ g₁)
    ≡⟨ cong₂ _+_ (Σᶻ-suc f) (Σᶻ-suc g) ⟨
  Σᶻ f + Σᶻ g
    ∎
  where
  open ≡-Reasoning

  f₀ f₁ g₀ g₁ : (Fin k → Bool) → ℤ
  f₀ z = f (false ∷ᵃ z)
  f₁ z = f (true  ∷ᵃ z)
  g₀ z = g (false ∷ᵃ z)
  g₁ z = g (true  ∷ᵃ z)

Σᶻ-* : (c : ℤ) (f : (Fin k → Bool) → ℤ) →
       Σᶻ (λ z → c * f z) ≡ c * Σᶻ f
Σᶻ-* {ℕ.zero}  c f = trans (Σᶻ-zero (λ z → c * f z))
  (cong (c *_) (sym (Σᶻ-zero f)))
Σᶻ-* {ℕ.suc k} c f = begin
  Σᶻ (λ z → c * f z)
    ≡⟨ Σᶻ-suc (λ z → c * f z) ⟩
  Σᶻ (λ z → c * f₀ z) + Σᶻ (λ z → c * f₁ z)
    ≡⟨ cong₂ _+_ (Σᶻ-* c f₀) (Σᶻ-* c f₁) ⟩
  c * Σᶻ f₀ + c * Σᶻ f₁
    ≡⟨ *-distribˡ-+ c (Σᶻ f₀) (Σᶻ f₁) ⟨
  c * (Σᶻ f₀ + Σᶻ f₁)
    ≡⟨ cong (c *_) (Σᶻ-suc f) ⟨
  c * Σᶻ f
    ∎
  where
  open ≡-Reasoning

  f₀ f₁ : (Fin k → Bool) → ℤ
  f₀ z = f (false ∷ᵃ z)
  f₁ z = f (true  ∷ᵃ z)

Σᶻ-0 : Σᶻ {k} (λ _ → 0ℤ) ≡ 0ℤ
Σᶻ-0 {ℕ.zero}  = Σᶻ-zero (λ _ → 0ℤ)
Σᶻ-0 {ℕ.suc k} =
  trans (Σᶻ-suc (λ _ → 0ℤ)) (cong₂ _+_ (Σᶻ-0 {k}) (Σᶻ-0 {k}))


------------------------------------------------------------------------
-- Positivity

Σᶻ-≥0 : (f : (Fin k → Bool) → ℤ) → (∀ z → 0ℤ ≤ f z) → 0ℤ ≤ Σᶻ f
Σᶻ-≥0 {ℕ.zero}  f f≥0 =
  ≤-trans (f≥0 (λ ())) (≤-reflexive (sym (Σᶻ-zero f)))
Σᶻ-≥0 {ℕ.suc k} f f≥0 = ≤-trans
  (+-mono-≤ (Σᶻ-≥0 (λ z → f (false ∷ᵃ z)) (λ z → f≥0 (false ∷ᵃ z)))
            (Σᶻ-≥0 (λ z → f (true  ∷ᵃ z)) (λ z → f≥0 (true  ∷ᵃ z))))
  (≤-reflexive (sym (Σᶻ-suc f)))

private
  -- Two non-negative integers adding up to zero are both zero.

  +≡0ˡ : ∀ {a b} → 0ℤ ≤ a → 0ℤ ≤ b → a + b ≡ 0ℤ → a ≡ 0ℤ
  +≡0ˡ {a} {b} a≥0 b≥0 eq = ≤-antisym
    (≤-trans (≤-reflexive (sym (+-identityʳ a)))
             (≤-trans (+-monoʳ-≤ a b≥0) (≤-reflexive eq)))
    a≥0

  +≡0ʳ : ∀ {a b} → 0ℤ ≤ a → 0ℤ ≤ b → a + b ≡ 0ℤ → b ≡ 0ℤ
  +≡0ʳ {a} {b} a≥0 b≥0 eq = +≡0ˡ b≥0 a≥0 (trans (+-comm b a) eq)

-- A vanishing sum of non-negative terms vanishes termwise.  Both
-- halves of the sum vanish, so the hypothesis covers the assignments
-- the recursion visits, and an arbitrary one is pointwise equal to
-- one of those.

Σᶻ-≡0 : (f : (Fin k → Bool) → ℤ) → (∀ z → 0ℤ ≤ f z) → RespectsZ f →
        Σᶻ f ≡ 0ℤ → ∀ z → f z ≡ 0ℤ
Σᶻ-≡0 {ℕ.zero}  f f≥0 resp eq z =
  trans (resp z (λ ()) (λ ())) (trans (sym (Σᶻ-zero f)) eq)
Σᶻ-≡0 {ℕ.suc k} f f≥0 resp eq z =
  trans (sym (resp _ z (∷ᵃ-η z))) (half (z zero) (λ i → z (suc i)))
  where
  f₀ f₁ : (Fin k → Bool) → ℤ
  f₀ g = f (false ∷ᵃ g)
  f₁ g = f (true  ∷ᵃ g)

  f₀≥0 : ∀ g → 0ℤ ≤ f₀ g
  f₀≥0 g = f≥0 (false ∷ᵃ g)

  f₁≥0 : ∀ g → 0ℤ ≤ f₁ g
  f₁≥0 g = f≥0 (true ∷ᵃ g)

  halves : Σᶻ f₀ + Σᶻ f₁ ≡ 0ℤ
  halves = trans (sym (Σᶻ-suc f)) eq

  half : ∀ b g → f (b ∷ᵃ g) ≡ 0ℤ
  half false = Σᶻ-≡0 f₀ f₀≥0 (respects-∷ᵃ resp false)
    (+≡0ˡ (Σᶻ-≥0 f₀ f₀≥0) (Σᶻ-≥0 f₁ f₁≥0) halves)
  half true  = Σᶻ-≡0 f₁ f₁≥0 (respects-∷ᵃ resp true)
    (+≡0ʳ (Σᶻ-≥0 f₀ f₀≥0) (Σᶻ-≥0 f₁ f₁≥0) halves)


------------------------------------------------------------------------
-- Splitting off one point

-- The sum is f x plus the sum with x masked out.  Comparing x with an
-- assignment starting with b compares x zero with b first, so in the
-- half of the sum where b differs from x zero nothing is masked, and
-- in the other half the mask is x's tail, which the hypothesis
-- splits off.

Σᶻ-point : (f : (Fin k → Bool) → ℤ) → RespectsZ f →
           ∀ (x : Fin k → Bool) →
           Σᶻ f ≡ f x + Σᶻ (λ z → if same x z then 0ℤ else f z)
Σᶻ-point {ℕ.zero}  f resp x = begin
  Σᶻ f
    ≡⟨ Σᶻ-zero f ⟩
  f (λ ())
    ≡⟨ resp (λ ()) x (λ ()) ⟩
  f x
    ≡⟨ +-identityʳ (f x) ⟨
  f x + 0ℤ
    ≡⟨ cong (f x +_) (Σᶻ-zero (λ z → if same x z then 0ℤ else f z)) ⟨
  f x + Σᶻ (λ z → if same x z then 0ℤ else f z)
    ∎
  where open ≡-Reasoning
Σᶻ-point {ℕ.suc k} f resp x = trans (split (x zero) refl)
  (cong (f x +_) (sym (Σᶻ-suc (λ z → if same x z then 0ℤ else f z))))
  where
  open ≡-Reasoning

  x′ : Fin k → Bool
  x′ j = x (suc j)

  -- The masked summand, with the head bit fixed to b.

  masked : Bool → (Fin k → Bool) → ℤ
  masked b g = if same x (b ∷ᵃ g) then 0ℤ else f (b ∷ᵃ g)

  -- In the half agreeing with x at the head, the mask is x′.

  agree : ∀ b → x zero ≡ b → ∀ g →
          (if same x′ g then 0ℤ else f (b ∷ᵃ g)) ≡ masked b g
  agree b eq g =
    cong (λ t → if t ∧ same x′ g then 0ℤ else f (b ∷ᵃ g))
         (sym (trans (cong (_=ᵇ b) eq) (=ᵇ-refl b)))

  -- In the other half nothing is masked.

  differ : ∀ b → (x zero =ᵇ b) ≡ false → ∀ g → f (b ∷ᵃ g) ≡ masked b g
  differ b ne g =
    cong (λ t → if t ∧ same x′ g then 0ℤ else f (b ∷ᵃ g)) (sym ne)

  -- x is its head bit followed by x′.

  head : ∀ b → x zero ≡ b → f (b ∷ᵃ x′) ≡ f x
  head b eq = resp (b ∷ᵃ x′) x pt
    where
    pt : ∀ j → (b ∷ᵃ x′) j ≡ x j
    pt zero    = sym eq
    pt (suc j) = refl

  -- The half agreeing with x, with f x split off, and the other half.

  on : ∀ b → x zero ≡ b →
       Σᶻ (λ g → f (b ∷ᵃ g)) ≡ f x + Σᶻ (masked b)
  on b eq = begin
    Σᶻ (λ g → f (b ∷ᵃ g))
      ≡⟨ Σᶻ-point (λ g → f (b ∷ᵃ g)) (respects-∷ᵃ resp b) x′ ⟩
    f (b ∷ᵃ x′) + Σᶻ (λ g → if same x′ g then 0ℤ else f (b ∷ᵃ g))
      ≡⟨ cong₂ _+_ (head b eq) (Σᶻ-cong (agree b eq)) ⟩
    f x + Σᶻ (masked b)
      ∎

  off : ∀ b → (x zero =ᵇ b) ≡ false →
        Σᶻ (λ g → f (b ∷ᵃ g)) ≡ Σᶻ (masked b)
  off b ne = Σᶻ-cong (differ b ne)

  split : ∀ b → x zero ≡ b →
          Σᶻ f ≡ f x + (Σᶻ (masked false) + Σᶻ (masked true))
  split false eq = begin
    Σᶻ f
      ≡⟨ Σᶻ-suc f ⟩
    Σᶻ (λ g → f (false ∷ᵃ g)) + Σᶻ (λ g → f (true ∷ᵃ g))
      ≡⟨ cong₂ _+_ (on false eq) (off true (cong (_=ᵇ true) eq)) ⟩
    (f x + Σᶻ (masked false)) + Σᶻ (masked true)
      ≡⟨ +-assoc (f x) (Σᶻ (masked false)) (Σᶻ (masked true)) ⟩
    f x + (Σᶻ (masked false) + Σᶻ (masked true))
      ∎
  split true  eq = begin
    Σᶻ f
      ≡⟨ Σᶻ-suc f ⟩
    Σᶻ (λ g → f (false ∷ᵃ g)) + Σᶻ (λ g → f (true ∷ᵃ g))
      ≡⟨ cong₂ _+_ (off false (cong (_=ᵇ false) eq)) (on true eq) ⟩
    Σᶻ (masked false) + (f x + Σᶻ (masked true))
      ≡⟨ x∙yz≈y∙xz (Σᶻ (masked false)) (f x) (Σᶻ (masked true)) ⟩
    f x + (Σᶻ (masked false) + Σᶻ (masked true))
      ∎


------------------------------------------------------------------------
-- Pairing the two values of one bit

-- The assignments giving i false each carry the pair: once with i
-- false, and once with it set to true.  At the head bit the pairing is
-- the sum's own split, the half giving the head true contributing
-- nothing; below it, the hypothesis applies to both halves, and an
-- update below the head commutes with fixing the head.

private
  -- Comparing two successors compares their predecessors.  The
  -- comparison is stuck on a neutral pair, so this takes a case split.

  ⌊≟⌋-suc : (j i : Fin k) → ⌊ suc j Fin.≟ suc i ⌋ ≡ ⌊ j Fin.≟ i ⌋
  ⌊≟⌋-suc j i with j Fin.≟ i
  ... | yes _ = refl
  ... | no  _ = refl

Σᶻ-at : (i : Fin k) (f : (Fin k → Bool) → ℤ) → RespectsZ f →
        Σᶻ f ≡ Σᶻ (λ z → if z i then 0ℤ
                         else (f (z [ i ≔ false ]) + f (z [ i ≔ true ])))
Σᶻ-at {ℕ.suc k} zero f resp = begin
  Σᶻ f
    ≡⟨ Σᶻ-suc f ⟩
  Σᶻ (λ g → f (false ∷ᵃ g)) + Σᶻ (λ g → f (true ∷ᵃ g))
    ≡⟨ Σᶻ-+ (λ g → f (false ∷ᵃ g)) (λ g → f (true ∷ᵃ g)) ⟨
  Σᶻ (λ g → f (false ∷ᵃ g) + f (true ∷ᵃ g))
    ≡⟨ Σᶻ-cong (λ g → cong₂ _+_ (resp _ _ (pt₀ g)) (resp _ _ (pt₁ g))) ⟩
  Σᶻ pair
    ≡⟨ +-identityʳ (Σᶻ pair) ⟨
  Σᶻ pair + 0ℤ
    ≡⟨ cong (Σᶻ pair +_) (Σᶻ-0 {k}) ⟨
  Σᶻ pair + Σᶻ {k} (λ _ → 0ℤ)
    ≡⟨ Σᶻ-suc paired ⟨
  Σᶻ paired
    ∎
  where
  open ≡-Reasoning

  paired : (Fin (ℕ.suc k) → Bool) → ℤ
  paired z = if z zero then 0ℤ
             else (f (z [ zero ≔ false ]) + f (z [ zero ≔ true ]))

  pair : (Fin k → Bool) → ℤ
  pair g = f ((false ∷ᵃ g) [ zero ≔ false ]) +
           f ((false ∷ᵃ g) [ zero ≔ true ])

  pt₀ : ∀ g j → (false ∷ᵃ g) j ≡ ((false ∷ᵃ g) [ zero ≔ false ]) j
  pt₀ g zero    = refl
  pt₀ g (suc j) = refl

  pt₁ : ∀ g j → (true ∷ᵃ g) j ≡ ((false ∷ᵃ g) [ zero ≔ true ]) j
  pt₁ g zero    = refl
  pt₁ g (suc j) = refl
Σᶻ-at {ℕ.suc k} (suc i) f resp =
  trans (Σᶻ-suc f) (trans (cong₂ _+_ (below false) (below true))
                          (sym (Σᶻ-suc paired)))
  where
  paired : (Fin (ℕ.suc k) → Bool) → ℤ
  paired z = if z (suc i) then 0ℤ
             else (f (z [ suc i ≔ false ]) + f (z [ suc i ≔ true ]))

  -- Updating bit i of the tail is updating bit suc i of the whole.

  shift : ∀ b g c j → (b ∷ᵃ (g [ i ≔ c ])) j ≡ ((b ∷ᵃ g) [ suc i ≔ c ]) j
  shift b g c zero    = refl
  shift b g c (suc j) =
    cong (λ t → if t then c else g j) (sym (⌊≟⌋-suc j i))

  below : ∀ b → Σᶻ (λ g → f (b ∷ᵃ g)) ≡ Σᶻ (λ g → paired (b ∷ᵃ g))
  below b = trans
    (Σᶻ-at i (λ g → f (b ∷ᵃ g)) (respects-∷ᵃ resp b))
    (Σᶻ-cong (λ g → cong (λ t → if g i then 0ℤ else t)
      (cong₂ _+_ (resp _ _ (shift b g false))
                 (resp _ _ (shift b g true)))))
