------------------------------------------------------------------------
-- Presentations of groups
--
-- Concatenated assignments, and the sums over them that composing
-- path-sums needs
--
-- The composite ξ′ ∘ ξ of definition 2.6 in Amy's QPL 2018 paper sums
-- over m + m′ path variables, ξ's first.  An assignment to them is the
-- concatenation y ++ᵃ y′ of one to ξ's and one to ξ′'s, and the sum
-- over all of them is the double sum (Σᴮ-++).  _++ᵃ_ is defined through
-- PathSum.Cyclotomic.extend, the constructor Σᴮ recurses with, so that
-- extend b y ++ᵃ y′ is extend b (y ++ᵃ y′) by definition and Σᴮ-++
-- needs no hypothesis on the summand.
--
-- The rest is the algebra of Z[ζ] that the proofs of proposition 2.7
-- use in place of a product: exchanging two sums (Σᴮ-swap), collapsing
-- a sum against a delta (Σᴮ-δ, for summands that read an assignment
-- only through its values), commuting rotations (rot-comm) and powers
-- of √2 with rotations and sums (scale-rot, scale-Σᴮ).  rot-comm and
-- scale-rot are PathSum.AmpLinear's linearity of rot and scale, and
-- scale-+ and scale-exp are AmpLinear's, re-exported.  Last, the guard
-- lemmas every amplitude computation needs, public here: several are
-- copies of private helpers of PathSum.CircuitAmp and
-- PathSum.CircuitSemantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Sum (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; _+_)
open import Data.Integer.Properties using (+-identityˡ; +-identityʳ)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.AmpLinear M₀ using (module Linear; rot-linear; scale-linear)
open import PathSum.AmpLinear M₀ public using (scale-+; scale-exp)
open import PathSum.Assign using (same)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; extend; Σᴮ; Σᴮ-+; Σᴮ-0; zpow; rot; rot-zpow;
   rot-0ᴬ; √2·; √2·-map; √2·-Σᴮ; scale; Respects)

private
  variable
    k l : ℕ


------------------------------------------------------------------------
-- Concatenated assignments

infixr 5 _++ᵃ_

_++ᵃ_ : (Fin k → Bool) → (Fin l → Bool) → (Fin (k ℕ+ l) → Bool)
_++ᵃ_ {zero}  y y′ = y′
_++ᵃ_ {suc k} y y′ = extend (y zero) ((λ i → y (suc i)) ++ᵃ y′)

-- Reading either block back.

++ᵃ-↑ˡ : (y : Fin k → Bool) (y′ : Fin l → Bool) (i : Fin k) →
         (y ++ᵃ y′) (i ↑ˡ l) ≡ y i
++ᵃ-↑ˡ y y′ zero    = refl
++ᵃ-↑ˡ y y′ (suc i) = ++ᵃ-↑ˡ (λ j → y (suc j)) y′ i

++ᵃ-↑ʳ : (y : Fin k → Bool) (y′ : Fin l → Bool) (i : Fin l) →
         (y ++ᵃ y′) (k ↑ʳ i) ≡ y′ i
++ᵃ-↑ʳ {zero}  y y′ i = refl
++ᵃ-↑ʳ {suc k} y y′ i = ++ᵃ-↑ʳ (λ j → y (suc j)) y′ i

-- Every assignment to k + l bits is, pointwise, the concatenation of
-- its two blocks.

++ᵃ-split : ∀ k l (x : Fin (k ℕ+ l) → Bool) (i : Fin (k ℕ+ l)) →
            ((λ i′ → x (i′ ↑ˡ l)) ++ᵃ (λ i′ → x (k ↑ʳ i′))) i ≡ x i
++ᵃ-split zero    l x i       = refl
++ᵃ-split (suc k) l x zero    = refl
++ᵃ-split (suc k) l x (suc i) = ++ᵃ-split k l (λ j → x (suc j)) i


------------------------------------------------------------------------
-- Sums over assignments

-- A sum over k + l bits is a double sum.  The sizes are explicit:
-- k ℕ+ l does not determine k.

Σᴮ-++ : ∀ k l (f : (Fin (k ℕ+ l) → Bool) → Amp) →
        Σᴮ f ≐ Σᴮ (λ y → Σᴮ (λ y′ → f (_++ᵃ_ {k} {l} y y′)))
Σᴮ-++ zero    l f i = refl
Σᴮ-++ (suc k) l f i = cong₂ _+_
  (Σᴮ-++ k l (λ g → f (extend true g)) i)
  (Σᴮ-++ k l (λ g → f (extend false g)) i)

-- Two sums commute.

Σᴮ-swap : (F : (Fin k → Bool) → (Fin l → Bool) → Amp) →
          Σᴮ (λ u → Σᴮ (λ v → F u v)) ≐ Σᴮ (λ v → Σᴮ (λ u → F u v))
Σᴮ-swap {zero}  F i = refl
Σᴮ-swap {suc k} F i = trans
  (cong₂ _+_ (Σᴮ-swap (λ u v → F (extend true u) v) i)
             (Σᴮ-swap (λ u v → F (extend false u) v) i))
  (sym (Σᴮ-+ (λ v → Σᴮ (λ u → F (extend true u) v))
             (λ v → Σᴮ (λ u → F (extend false u) v)) i))

-- A delta collapses a sum, for a summand that reads assignments only
-- through their values.  The induction is over assignments whose head
-- is a constructor, extend b u′, so that the test against the head of
-- each summand's assignment computes.

private
  extend-≗ : (b : Bool) {g h : Fin k → Bool} → (∀ j → g j ≡ h j) →
             ∀ j → extend b g j ≡ extend b h j
  extend-≗ b g≗h zero    = refl
  extend-≗ b g≗h (suc j) = g≗h j

  respects-extend : (F : (Fin (suc k) → Bool) → Amp) → Respects F →
                    ∀ b → Respects (λ g → F (extend b g))
  respects-extend F resp b g h g≗h = resp (extend b g) (extend b h) (extend-≗ b g≗h)

Σᴮ-δ : (u : Fin k → Bool) (F : (Fin k → Bool) → Amp) → Respects F →
       Σᴮ (λ w → if same u w then F w else 0ᴬ) ≐ F u

private
  Σᴮ-δ-extend : (b : Bool) (u : Fin k → Bool) (F : (Fin (suc k) → Bool) → Amp) →
                Respects F →
                Σᴮ (λ w → if same (extend b u) w then F w else 0ᴬ) ≐
                F (extend b u)
  Σᴮ-δ-extend {k} true u F resp i = trans
    (cong₂ _+_ (Σᴮ-δ u (λ g → F (extend true g))
                        (respects-extend F resp true) i)
               (Σᴮ-0 {k} i))
    (+-identityʳ (F (extend true u) i))
  Σᴮ-δ-extend {k} false u F resp i = trans
    (cong₂ _+_ (Σᴮ-0 {k} i)
               (Σᴮ-δ u (λ g → F (extend false g))
                        (respects-extend F resp false) i))
    (+-identityˡ (F (extend false u) i))

Σᴮ-δ {zero}  u F resp = resp (λ ()) u (λ ())
Σᴮ-δ {suc k} u F resp i = trans
  (Σᴮ-δ-extend (u zero) (λ j → u (suc j)) F resp i)
  (resp (extend (u zero) (λ j → u (suc j))) u η i)
  where
  η : ∀ j → extend (u zero) (λ j → u (suc j)) j ≡ u j
  η zero    = refl
  η (suc j) = refl


------------------------------------------------------------------------
-- Rotations and powers of √2

-- Multiplications by powers of ζ commute.

rot-comm : ∀ e e′ a → rot e (rot e′ a) ≐ rot e′ (rot e a)
rot-comm e = Linear.map-rot (rot-linear e)

-- A power of √2 commutes with rotations and with sums.

scale-rot : ∀ i e a → scale i (rot e a) ≐ rot e (scale i a)
scale-rot i = Linear.map-rot (scale-linear i)

scale-Σᴮ : ∀ i (f : (Fin k → Bool) → Amp) →
           scale i (Σᴮ f) ≐ Σᴮ (λ y → scale i (f y))
scale-Σᴮ zero    f _ = refl
scale-Σᴮ (suc i) f j = trans (√2·-map (scale-Σᴮ i f) j)
                             (√2·-Σᴮ (λ y → scale i (f y)) j)


------------------------------------------------------------------------
-- Guards

-- A Boolean determined by two implications.

bool-iff : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
           a ≡ b
bool-iff {true}  {true}  _ _ = refl
bool-iff {true}  {false} f _ = sym (f refl)
bool-iff {false} {true}  _ g = g refl
bool-iff {false} {false} _ _ = refl

-- Guarded amplitudes are congruences in guard and value.

if-cong : {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
          (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
if-cong {p = true}  refl a≐b = a≐b
if-cong {p = false} refl _   = λ _ → refl

zpow-≡ : {a b : ℤ} → a ≡ b → zpow a ≐ zpow b
zpow-≡ refl _ = refl

-- Rotating a guarded amplitude rotates its value; for a guarded power
-- of ζ, it adds to the exponent.

rot-guard : (c : Bool) (e : ℤ) (a : Amp) →
            rot e (if c then a else 0ᴬ) ≐ (if c then rot e a else 0ᴬ)
rot-guard true  e a = λ _ → refl
rot-guard false e a = rot-0ᴬ e

rot-if : (p : Bool) (e a : ℤ) →
         rot e (if p then zpow a else 0ᴬ) ≐ (if p then zpow (e + a) else 0ᴬ)
rot-if true  e a = rot-zpow e a
rot-if false e a = rot-0ᴬ e

-- A guard passes through a sum.

if-Σᴮ : (c : Bool) (f : (Fin k → Bool) → Amp) →
        (if c then Σᴮ f else 0ᴬ) ≐ Σᴮ (λ y → if c then f y else 0ᴬ)
if-Σᴮ         true  f _ = refl
if-Σᴮ {k = k} false f i = sym (Σᴮ-0 {k} i)
