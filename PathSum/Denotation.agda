------------------------------------------------------------------------
-- Presentations of groups
--
-- The denotation of a path-sum, and equivalence of path-sums
-- (Amy, QPL 2018, definitions 2.1 and 2.3)
--
-- The operator of a path-sum is
--
--    |x⟩ ↦ 1/√2^k Σ_{y ∈ Z₂^m} e^{2πi P(x,y)} |f (x , y)⟩,
--
-- whose matrix entry from x to z is 1/√2^k times a sum of powers of
-- ζ, that is, an element of Z[ζ] divided by √2^k.  The normalisation
-- k is kept apart from the number m of path variables: definition 2.1
-- ties them together, but the rules of figure 2 do not preserve that
-- tie -- [HH] leaves the normalisation alone while removing a path
-- variable -- so a path-sum is paired here with its own exponent.
--
-- Two path-sums are equivalent when their operators agree, which
-- after clearing denominators is an identity in Z[ζ]: cross-multiply
-- by the two normalisations.  Transitivity of that relation is not
-- formal: it needs the factor √2^k to be cancellable, which is
-- PathSum.Cyclotomic.scale-injective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Denotation (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_;
  if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _-_; _*_)
  renaming (_+_ to _+ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣m∣n⇒∣m+n; ∣m+n∣m⇒∣n)
open import Data.Integer.Properties using (+-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

open import PathSum.Base
open import PathSum.Cyclotomic M₀
open import PathSum.Order (suc (suc (suc M₀)))
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties
open import PathSum.Reduction (suc (suc (suc M₀)))

import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Assignments

Assign : ℕ → Set
Assign k = Fin k → Bool

private
  eqᵇ : Bool → Bool → Bool
  eqᵇ a b = not (a xor b)

  allFin : ∀ {k} → (Fin k → Bool) → Bool
  allFin {zero}  _ = true
  allFin {suc k} f = f zero ∧ allFin (λ i → f (suc i))

  -- The output polynomials are read modulo 2.
  bit : ℤ → Bool
  bit z = not ⌊ (+ 2) ∣? z ⌋

-- Whether the path y carries the input x to the output z.

hits : PathSum n k m → Assign n → Assign m → Assign n → Bool
hits ξ x y z = allFin (λ w → eqᵇ (bit (eval (out ξ w) x y)) (z w))


------------------------------------------------------------------------
-- The unnormalised amplitude

-- The entry of the operator from x to z, before dividing by √2^k:
-- the sum of ζ^P over the paths that hit z.

amp : PathSum n k m → Assign n → Assign n → Amp
amp ξ x z = Σᴮ (λ y → if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ)


------------------------------------------------------------------------
-- Splitting off the first path variable

-- Evaluating at an assignment that sends y₀ to false ignores the
-- terms containing y₀; sending it to true adds them in.

eval-false : (P : Poly n (suc m)) (x : Assign n) (y : Assign m) →
             eval P x (extend false y) ≡ eval (tail-part P) x y
eval-false {n} {m} P x y = Σsub-cong (λ α →
  trans (cong (_+ℤ tailSum α) (trans (Σsub-cong (inner α)) (Σsub-0 {m})))
        (+-identityˡ (tailSum α)))
  where
  tailSum : Subset n → ℤ
  tailSum α =
    Σsub (λ β → if satᵐ (α , β) x y then tail-part P (α , β) else 0ℤ)

  inner : ∀ (α : Subset n) (β : Subset m) →
          (if (sat α x ∧ false) then P (α , inside ∷ β) else 0ℤ) ≡ 0ℤ
  inner α β rewrite ∧-zeroʳ (sat α x) = refl

eval-true : (P : Poly n (suc m)) (x : Assign n) (y : Assign m) →
            eval P x (extend true y) ≡
            eval (head-part P) x y +ℤ eval (tail-part P) x y
eval-true {n} {m} P x y = Σsub-+ headSum tailSum
  where
  headSum tailSum : Subset n → ℤ
  headSum α =
    Σsub (λ β → if satᵐ (α , β) x y then head-part P (α , β) else 0ℤ)
  tailSum α =
    Σsub (λ β → if satᵐ (α , β) x y then tail-part P (α , β) else 0ℤ)

private
  allFin-cong : ∀ {j} {f g : Fin j → Bool} → (∀ w → f w ≡ g w) →
                allFin f ≡ allFin g
  allFin-cong {zero}  f≗g = refl
  allFin-cong {suc j} f≗g =
    cong₂ _∧_ (f≗g zero) (allFin-cong (λ w → f≗g (suc w)))

  -- Adding an even number does not change a bit.
  bit-even : ∀ {a} b → (+ 2) ∣ a → bit (a +ℤ b) ≡ bit b
  bit-even {a} b d with (+ 2) ∣? (a +ℤ b) | (+ 2) ∣? b
  ... | yes _ | yes _  = refl
  ... | yes p | no  ¬q = contradiction (∣m+n∣m⇒∣n p d) ¬q
  ... | no  ¬p | yes q = contradiction (∣m∣n⇒∣m+n d q) ¬p
  ... | no  _ | no  _  = refl

-- Definition 2.3.  U_ξ = U_ζ says that amp ξ/√2^k and amp ζ/√2^k′
-- agree, which cleared of denominators is the identity below in Z[ζ].

infix 4 _≋_

_≋_ : PathSum n k m → PathSum n k′ m′ → Set
_≋_ {k = k} {k′ = k′} ξ ζ =
  ∀ x z → scale k′ (amp ξ x z) ≐ scale k (amp ζ x z)

private
  scale-+ : ∀ a b w → scale a (scale b w) ≐ scale (a ℕ+ b) w
  scale-+ zero    b w _ = refl
  scale-+ (suc a) b w   = √2·-map (scale-+ a b w)

  scale-exp : ∀ {a b} w → a ≡ b → scale a w ≐ scale b w
  scale-exp w refl _ = refl

≋-refl : {ξ : PathSum n k m} → ξ ≋ ξ
≋-refl _ _ _ = refl

≋-sym : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ≋ ζ → ζ ≋ ξ
≋-sym ξ≋ζ x z i = sym (ξ≋ζ x z i)

-- Transitivity is where the cancellation of √2 is needed: scaling
-- both hypotheses to a common normalisation leaves a factor
-- √2^(norm ζ) on either side, which scale-injective removes.

≋-trans : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} {χ : PathSum n k″ m″} →
          ξ ≋ ζ → ζ ≋ χ → ξ ≋ χ
≋-trans {k = a} {k′ = b} {k″ = d} {ξ = ξ} {ζ} {χ} ξ≋ζ ζ≋χ x z =
  scale-injective b (scale d A) (scale a C) common
  where
  A = amp ξ x z
  B = amp ζ x z
  C = amp χ x z

  -- Scaling the first hypothesis by √2^d and the second by √2^a
  -- brings both to the normalisation a + b + d.

  left : ∀ i → scale (d ℕ+ b) A i ≡ scale (d ℕ+ a) B i
  left i = trans (sym (scale-+ d b A i))
                 (trans (scale-map d (ξ≋ζ x z) i) (scale-+ d a B i))

  right : ∀ i → scale (a ℕ+ d) B i ≡ scale (a ℕ+ b) C i
  right i = trans (sym (scale-+ a d B i))
                  (trans (scale-map a (ζ≋χ x z) i) (scale-+ a b C i))

  common : ∀ i → scale b (scale d A) i ≡ scale b (scale a C) i
  common i = trans (scale-+ b d A i)
    (trans (scale-exp A (ℕ.+-comm b d) i)
      (trans (left i)
        (trans (scale-exp B (ℕ.+-comm d a) i)
          (trans (right i)
            (trans (scale-exp C (ℕ.+-comm a b) i)
                   (sym (scale-+ b a C i)))))))



------------------------------------------------------------------------
-- Soundness of [Elim]

-- If y₀ occurs neither in the phase nor in the outputs, the two
-- branches of the sum over y₀ contribute the same thing, so the
-- amplitude of ξ is twice that of its reduct -- and 2 = √2·√2 pays
-- for exactly the two units of normalisation the rule consumes.

private
  M : ℕ
  M = suc (suc (suc M₀))

  if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl a≐b = λ _ → refl

  twice : ∀ q → q +ℤ q ≡ (+ 2) * q
  twice = solve 1 (λ q → q :+ q := con (+ 2) :* q) refl

module _ {n k m : ℕ} (ξ : PathSum n (suc (suc k)) (suc m))
         (eqP : head-part (phase ξ) ≈[ pow M ] 0ᴾ)
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  private
    -- Every coefficient of the y₀-part of an output is even, and of
    -- the y₀-part of the phase is zero modulo 2^M.
    head-out : ∀ w γ → (+ 2) ∣ head-part (out ξ w) γ
    head-out w (α , β) = eqf w (α , inside ∷ β) here

    head-phase : ∀ γ → pow M ∣ head-part (phase ξ) γ
    head-phase γ = Eq.subst (pow M ∣_)
      (+-identityʳ (head-part (phase ξ) γ)) (eqP γ)

    out-bit : ∀ (b : Bool) (x : Assign n) (y : Assign m) w →
              bit (eval (out ξ w) x (extend b y)) ≡
              bit (eval (tail-part (out ξ w)) x y)
    out-bit false x y w = cong bit (eval-false (out ξ w) x y)
    out-bit true  x y w = trans (cong bit (eval-true (out ξ w) x y))
      (bit-even _ (eval-∣ (head-part (out ξ w)) (head-out w) x y))

    same-hits : ∀ (b : Bool) (x z : Assign n) (y : Assign m) →
                hits ξ x (extend b y) z ≡ hits (elim-reduct ξ) x y z
    same-hits b x z y =
      allFin-cong (λ w → cong (λ v → eqᵇ v (z w)) (out-bit b x y w))

    same-phase : ∀ (b : Bool) (x : Assign n) (y : Assign m) →
                 zpow (eval (phase ξ) x (extend b y)) ≐
                 zpow (eval (tail-part (phase ξ)) x y)
    same-phase false x y i =
      cong (λ v → zpow v i) (eval-false (phase ξ) x y)
    same-phase true x y i =
      trans (cong (λ v → zpow v i) (eval-true (phase ξ) x y))
            (zpow-cong {eval (head-part (phase ξ)) x y +ℤ
                        eval (tail-part (phase ξ)) x y}
                       {eval (tail-part (phase ξ)) x y} shifted i)
      where
      drop : ∀ u v → (u +ℤ v) - v ≡ u
      drop = solve 2 (λ u v → (u :+ v) :- v := u) refl

      shifted : (+ N) ∣ ((eval (head-part (phase ξ)) x y +ℤ
                          eval (tail-part (phase ξ)) x y) -
                         eval (tail-part (phase ξ)) x y)
      shifted = Eq.subst ((+ N) ∣_)
        (sym (drop (eval (head-part (phase ξ)) x y)
                   (eval (tail-part (phase ξ)) x y)))
        (eval-∣ (head-part (phase ξ)) head-phase x y)

  branch : ∀ (b : Bool) (x z : Assign n) (y : Assign m) →
           (if hits ξ x (extend b y) z
            then zpow (eval (phase ξ) x (extend b y)) else 0ᴬ)
           ≐ (if hits (elim-reduct ξ) x y z
              then zpow (eval (tail-part (phase ξ)) x y) else 0ᴬ)
  branch b x z y = if-cong (same-hits b x z y) (same-phase b x y)

  amp-elim : ∀ x z → amp ξ x z ≐ (+ 2) ·ᴬ amp (elim-reduct ξ) x z
  amp-elim x z i = trans
    (Eq.cong₂ _+ℤ_ (Σᴮ-cong (branch true x z) i)
                   (Σᴮ-cong (branch false x z) i))
    (twice (amp (elim-reduct ξ) x z i))

  elim-sound : ξ ≋ elim-reduct ξ
  elim-sound x z i = trans (scale-map k (amp-elim x z) i)
    (trans (scale-·ᴬ k (+ 2) (amp (elim-reduct ξ) x z) i)
           (sym (√2·-twice (scale k (amp (elim-reduct ξ) x z)) i)))
