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

-- The interference proofs below normalise sums over every assignment
-- to the path variables; under call-by-need the shared subterms of
-- those sums are duplicated and the module exhausts memory, so this
-- file is checked call-by-name.

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Denotation (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_;
  if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; ⊥; _∈_)
  renaming (_-_ to _∖ᶠ_)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _-_; _*_)
  renaming (_+_ to _+ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣-refl; ∣m∣n⇒∣m+n; ∣m+n∣m⇒∣n)
open import Data.Integer.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ;
   *-identityʳ; *-identityˡ; *-zeroʳ; *-zeroˡ; neg-involutive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _<_; s≤s; z≤n)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base
open import PathSum.Cyclotomic M₀
open import PathSum.Order (suc (suc (suc M₀)))
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties
open import PathSum.Reduction (suc (suc (suc M₀)))
open import PathSum.Semantics (suc (suc (suc M₀))) using (Semantics)

import Data.Fin.Properties as Fin
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

-- The outputs of every reduct are the y₀-free parts of ξ's, so the
-- set of paths hitting a given output does not change.

module _ {n k m : ℕ} (ξ : PathSum n k (suc m))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  head-out : ∀ w γ → (+ 2) ∣ head-part (out ξ w) γ
  head-out w (α , β) = eqf w (α , inside ∷ β) here

  out-bit : ∀ (b : Bool) (x : Assign n) (y : Assign m) w →
            bit (eval (out ξ w) x (extend b y)) ≡
            bit (eval (tail-part (out ξ w)) x y)
  out-bit false x y w = cong bit (eval-false (out ξ w) x y)
  out-bit true  x y w = trans (cong bit (eval-true (out ξ w) x y))
    (bit-even _ (eval-∣ (head-part (out ξ w)) (head-out w) x y))

  same-hits : ∀ (b : Bool) (x z : Assign n) (y : Assign m) →
              hits ξ x (extend b y) z ≡
              allFin (λ w → eqᵇ (bit (eval (tail-part (out ξ w)) x y)) (z w))
  same-hits b x z y =
    allFin-cong (λ w → cong (λ v → eqᵇ v (z w)) (out-bit b x y w))


module _ {n k m : ℕ} (ξ : PathSum n (suc (suc k)) (suc m))
         (eqP : head-part (phase ξ) ≈[ pow M ] 0ᴾ)
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  private
    head-phase : ∀ γ → pow M ∣ head-part (phase ξ) γ
    head-phase γ = Eq.subst (pow M ∣_)
      (+-identityʳ (head-part (phase ξ) γ)) (eqP γ)

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
  branch b x z y = if-cong (same-hits ξ eqf b x z y) (same-phase b x y)

  amp-elim : ∀ x z → amp ξ x z ≐ (+ 2) ·ᴬ amp (elim-reduct ξ) x z
  amp-elim x z i = trans
    (Eq.cong₂ _+ℤ_ (Σᴮ-cong (branch true x z) i)
                   (Σᴮ-cong (branch false x z) i))
    (twice (amp (elim-reduct ξ) x z i))

  elim-sound : ξ ≋ elim-reduct ξ
  elim-sound x z i = trans (scale-map k (amp-elim x z) i)
    (trans (scale-·ᴬ k (+ 2) (amp (elim-reduct ξ) x z) i)
           (sym (√2·-twice (scale k (amp (elim-reduct ξ) x z)) i)))


------------------------------------------------------------------------
-- Soundness of [ω]

-- Summing the two branches of y₀ over a phase ¼y₀ + ½y₀Q + R gives
-- 1 + i(-1)^Q times e^{2πiR}, which is √2 e^{2πi(⅛ - ¼Q)} times it.
-- That is the identity below, once Q is known to be 0 or 1.

private
  ⅛+⅛ : ⅛ +ℤ ⅛ ≡ ¼
  ⅛+⅛ = trans (double ⅛) (sym (pow-suc M₀))
    where
    double : ∀ u → u +ℤ u ≡ u * (+ 2)
    double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  ¼+¼ : ¼ +ℤ ¼ ≡ ½
  ¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))
    where
    double : ∀ u → u +ℤ u ≡ u * (+ 2)
    double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  ½+½ : ½ +ℤ ½ ≡ pow M
  ½+½ = trans (double ½) (sym (pow-suc (suc (suc M₀))))
    where
    double : ∀ u → u +ℤ u ≡ u * (+ 2)
    double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  drop-t : ∀ a b t → (a +ℤ t) - (b +ℤ t) ≡ a - b
  drop-t = solve 3 (λ a b t → (a :+ t) :- (b :+ t) := a :- b) refl

  pull : ∀ u t → u +ℤ (u +ℤ t) ≡ (u +ℤ u) +ℤ t
  pull = solve 2 (λ u t → u :+ (u :+ t) := (u :+ u) :+ t) refl

  pull′ : ∀ w u v t → w +ℤ ((u - v) +ℤ t) ≡ ((w +ℤ u) - v) +ℤ t
  pull′ = solve 4 (λ w u v t →
    w :+ ((u :- v) :+ t) := ((w :+ u) :- v) :+ t) refl

  cancel-neg : ∀ u t → (- u) +ℤ (u +ℤ t) ≡ t
  cancel-neg u t = trans (sym (+-assoc (- u) u t))
    (trans (cong (_+ℤ t) (+-inverseˡ u)) (+-identityˡ t))

  -- √2 · ζ^(⅛+t) = ζ^(¼+t) + ζ^t
  ω-split₀ : ∀ t → √2· (zpow (⅛ +ℤ t)) ≐ zpow (¼ +ℤ t) +ᴬ zpow t
  ω-split₀ t i = trans (√2·-zpow (⅛ +ℤ t) i)
    (Eq.cong₂ _+ℤ_
      (cong (λ w → zpow w i) (trans (pull ⅛ t) (cong (_+ℤ t) ⅛+⅛)))
      (cong (λ w → zpow w i) (cancel-neg ⅛ t)))

  -- √2 · ζ^(⅛-¼+t) = ζ^t + ζ^(-¼+t)
  ω-split₁ : ∀ t → √2· (zpow ((⅛ - ¼) +ℤ t)) ≐
                   zpow t +ᴬ zpow ((- ¼) +ℤ t)
  ω-split₁ t i = trans (√2·-zpow ((⅛ - ¼) +ℤ t) i)
    (Eq.cong₂ _+ℤ_ (cong (λ w → zpow w i) fst) (cong (λ w → zpow w i) snd))
    where
    fst : ⅛ +ℤ ((⅛ - ¼) +ℤ t) ≡ t
    fst = trans (pull′ ⅛ ⅛ ¼ t)
      (trans (cong (λ w → (w - ¼) +ℤ t) ⅛+⅛)
        (trans (cong (_+ℤ t) (+-inverseʳ ¼)) (+-identityˡ t)))

    snd : (- ⅛) +ℤ ((⅛ - ¼) +ℤ t) ≡ (- ¼) +ℤ t
    snd = trans (pull′ (- ⅛) ⅛ ¼ t)
      (trans (cong (λ w → (w - ¼) +ℤ t) (+-inverseˡ ⅛))
             (cong (_+ℤ t) (+-identityˡ (- ¼))))

  interfere₀ : (hv t : ℤ) → pow M ∣ (hv - ¼) →
               (zpow (hv +ℤ t) +ᴬ zpow t) ≐ √2· (zpow (⅛ +ℤ t))
  interfere₀ hv t div i = trans
    (Eq.cong₂ _+ℤ_
      (zpow-cong {hv +ℤ t} {¼ +ℤ t}
        (Eq.subst ((+ N) ∣_) (sym (drop-t hv ¼ t)) div) i)
      refl)
    (sym (ω-split₀ t i))

  interfere₁ : (hv t : ℤ) → pow M ∣ (hv - (¼ +ℤ ½)) →
               (zpow (hv +ℤ t) +ᴬ zpow t) ≐ √2· (zpow ((⅛ - ¼) +ℤ t))
  interfere₁ hv t div i = trans
    (Eq.cong₂ _+ℤ_
      (trans (zpow-cong {hv +ℤ t} {(¼ +ℤ ½) +ℤ t}
               (Eq.subst ((+ N) ∣_) (sym (drop-t hv (¼ +ℤ ½) t)) div) i)
             (zpow-cong {(¼ +ℤ ½) +ℤ t} {(- ¼) +ℤ t} big i))
      refl)
    (trans (+ᴬ-comm (zpow ((- ¼) +ℤ t)) (zpow t) i) (sym (ω-split₁ t i)))
    where
    reshape : ∀ a b w t′ → ((a +ℤ b) +ℤ t′) - (w +ℤ t′) ≡ (a +ℤ b) - w
    reshape = solve 4 (λ a b w t′ →
      ((a :+ b) :+ t′) :- (w :+ t′) := (a :+ b) :- w) refl

    regroup : ∀ a b → (a +ℤ b) +ℤ a ≡ (a +ℤ a) +ℤ b
    regroup = solve 2 (λ a b → (a :+ b) :+ a := (a :+ a) :+ b) refl

    value : ((¼ +ℤ ½) +ℤ t) - ((- ¼) +ℤ t) ≡ pow M
    value = trans (reshape ¼ ½ (- ¼) t)
      (trans (cong ((¼ +ℤ ½) +ℤ_) (neg-involutive ¼))
        (trans (regroup ¼ ½) (trans (cong (_+ℤ ½) ¼+¼) ½+½)))

    big : (+ N) ∣ (((¼ +ℤ ½) +ℤ t) - ((- ¼) +ℤ t))
    big = Eq.subst ((+ N) ∣_) (sym value) ∣-refl

module _ {n k m : ℕ} (ξ : PathSum n (suc k) (suc m)) (c : Bool)
         (S : Mon n m)
         (eqP : head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  private
    red : PathSum n k m
    red = ω-reduct ξ c S

    qv : Assign n → Assign m → ℤ
    qv x y = eval (liftXor c S) x y

    tv : Assign n → Assign m → ℤ
    tv x y = eval (tail-part (phase ξ)) x y

    red-eval : ∀ x y → eval (phase red) x y ≡
               (⅛ - (¼ * qv x y)) +ℤ tv x y
    red-eval x y = trans
      (eval-+ᴾ (κ ⅛ -ᴾ (¼ ·ᴾ liftXor c S)) (tail-part (phase ξ)) x y)
      (cong (_+ℤ tv x y)
        (trans (eval-−ᴾ (κ ⅛) (¼ ·ᴾ liftXor c S) x y)
          (cong₂ _-_ (eval-κ ⅛ x y) (eval-·ᴾ ¼ (liftXor c S) x y))))

    head-eval : ∀ x y →
                pow M ∣ (eval (head-part (phase ξ)) x y -
                         (¼ +ℤ (½ * qv x y)))
    head-eval x y = Eq.subst
      (λ w → pow M ∣ (eval (head-part (phase ξ)) x y - w))
      (trans (eval-+ᴾ (κ ¼) (½ ·ᴾ liftXor c S) x y)
             (cong₂ _+ℤ_ (eval-κ ¼ x y) (eval-·ᴾ ½ (liftXor c S) x y)))
      (eval-≈ (head-part (phase ξ)) (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) eqP x y)

    -- The two branches of y₀ interfere into √2 times the reduct.

    core : ∀ x y →
           (zpow (eval (head-part (phase ξ)) x y +ℤ tv x y) +ᴬ zpow (tv x y))
           ≐ √2· (zpow ((⅛ - (¼ * qv x y)) +ℤ tv x y))
    core x y with liftXor-value c S x y
    ... | inj₁ q≡0 = λ i → trans
      (interfere₀ (eval (head-part (phase ξ)) x y) (tv x y) div i)
      (cong (λ w → √2· (zpow (w +ℤ tv x y)) i) (sym at0))
      where
      at0 : ⅛ - (¼ * qv x y) ≡ ⅛
      at0 = trans (cong (λ w → ⅛ - (¼ * w)) q≡0)
                  (trans (cong (λ v → ⅛ - v) (*-zeroʳ ¼)) (+-identityʳ ⅛))

      div : pow M ∣ (eval (head-part (phase ξ)) x y - ¼)
      div = Eq.subst (λ w → pow M ∣ (eval (head-part (phase ξ)) x y - w))
        (trans (cong (λ w → ¼ +ℤ (½ * w)) q≡0)
               (trans (cong (λ v → ¼ +ℤ v) (*-zeroʳ ½)) (+-identityʳ ¼)))
        (head-eval x y)
    ... | inj₂ q≡1 = λ i → trans
      (interfere₁ (eval (head-part (phase ξ)) x y) (tv x y) div i)
      (cong (λ w → √2· (zpow (w +ℤ tv x y)) i) (sym at1))
      where
      at1 : ⅛ - (¼ * qv x y) ≡ ⅛ - ¼
      at1 = trans (cong (λ w → ⅛ - (¼ * w)) q≡1)
                  (cong (λ v → ⅛ - v) (*-identityʳ ¼))

      div : pow M ∣ (eval (head-part (phase ξ)) x y - (¼ +ℤ ½))
      div = Eq.subst (λ w → pow M ∣ (eval (head-part (phase ξ)) x y - w))
        (trans (cong (λ w → ¼ +ℤ (½ * w)) q≡1)
               (cong (λ v → ¼ +ℤ v) (*-identityʳ ½)))
        (head-eval x y)

    -- Stated over an arbitrary ζ carrying the reduct's denotational
    -- data, so that ω-reduct never unfolds inside the proof.

    if-guard : ∀ {p q : Bool} {a : Amp} → p ≡ q →
               (if p then a else 0ᴬ) ≐ (if q then a else 0ᴬ)
    if-guard refl _ = refl

    if-sum : ∀ (p : Bool) (a b r : Amp) → (a +ᴬ b) ≐ √2· r →
             ((if p then a else 0ᴬ) +ᴬ (if p then b else 0ᴬ)) ≐
             √2· (if p then r else 0ᴬ)
    if-sum true  a b r h = h
    if-sum false a b r h = λ i → sym (√2·-0ᴬ i)

    -- Naming the summand of each amplitude keeps the goals below from
    -- carrying the whole body as a lambda.

    bξ : Assign n → Assign n → Assign (suc m) → Amp
    bξ x z y′ = if hits ξ x y′ z then zpow (eval (phase ξ) x y′) else 0ᴬ

    bζ : (ζ : PathSum n k m) → Assign n → Assign n → Assign m → Amp
    bζ ζ x z y = if hits ζ x y z then zpow (eval (phase ζ) x y) else 0ᴬ

    ω-step : (ζ : PathSum n k m) →
             (∀ x y z → hits ζ x y z ≡
                allFin (λ w → eqᵇ (bit (eval (tail-part (out ξ w)) x y))
                                  (z w))) →
             (∀ x y → eval (phase ζ) x y ≡
                      (⅛ - (¼ * qv x y)) +ℤ tv x y) →
             ∀ (x z : Assign n) (y : Assign m) →
             (bξ x z (extend true y) +ᴬ bξ x z (extend false y))
             ≐ √2· (bζ ζ x z y)
    ω-step ζ hζ pζ x z y i = trans
      (Eq.cong₂ _+ℤ_
        (if-guard (trans (same-hits ξ eqf true x z y) (sym (hζ x y z))) i)
        (if-guard (trans (same-hits ξ eqf false x z y) (sym (hζ x y z))) i))
      (if-sum (hits ζ x y z)
        (zpow (eval (phase ξ) x (extend true y)))
        (zpow (eval (phase ξ) x (extend false y)))
        (zpow (eval (phase ζ) x y)) inner i)
      where
      inner : (zpow (eval (phase ξ) x (extend true y)) +ᴬ
               zpow (eval (phase ξ) x (extend false y)))
              ≐ √2· (zpow (eval (phase ζ) x y))
      inner i″ = trans
        (Eq.cong₂ _+ℤ_
          (cong (λ w → zpow w i″) (eval-true (phase ξ) x y))
          (cong (λ w → zpow w i″) (eval-false (phase ξ) x y)))
        (trans (core x y i″)
               (cong (λ w → √2· (zpow w) i″) (sym (pζ x y))))

    amp-gen : (ζ : PathSum n k m) →
              (∀ x y z → hits ζ x y z ≡
                 allFin (λ w → eqᵇ (bit (eval (tail-part (out ξ w)) x y))
                                   (z w))) →
              (∀ x y → eval (phase ζ) x y ≡
                       (⅛ - (¼ * qv x y)) +ℤ tv x y) →
              ∀ x z → amp ξ x z ≐ √2· (amp ζ x z)
    amp-gen ζ hζ pζ x z i = trans
      (sym (Σᴮ-+ (λ y → bξ x z (extend true y))
                 (λ y → bξ x z (extend false y)) i))
      (trans (Σᴮ-cong (ω-step ζ hζ pζ x z) i)
             (sym (√2·-Σᴮ (bζ ζ x z) i)))

  ω-sound : ξ ≋ ω-reduct ξ c S
  ω-sound x z i = trans
    (scale-map k (amp-gen (ω-reduct ξ c S) (λ _ _ _ → refl) red-eval x z) i)
    (scale-√2 k (amp (ω-reduct ξ c S) x z) i)


------------------------------------------------------------------------
-- Soundness of [HH]

-- The premise makes the head of the phase ½ times the form on S, so
-- the two branches of y₀ carry the same phase where the form vanishes
-- and opposite phases where it is 1.

------------------------------------------------------------------------
-- Cancellation of the two branches of y₀

-- Shared by [HH] and by lemma 4.2: when the head of the phase is a
-- half times the form on S, the two branches of y₀ double where the
-- form vanishes and cancel where it is 1.

module Cancel {n k m : ℕ} (ξ : PathSum n k (suc m)) (c : Bool)
              (S : Mon n m)
              (eqP : head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S))
              (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
              where

  tv hd : Assign n → Assign m → ℤ
  tv x y = eval (tail-part (phase ξ)) x y
  hd x y = eval (head-part (phase ξ)) x y

  head-eval : ∀ x y →
              pow M ∣ (hd x y - (½ * eval (liftXor c S) x y))
  head-eval x y = Eq.subst (λ w → pow M ∣ (hd x y - w))
    (eval-·ᴾ ½ (liftXor c S) x y)
    (eval-≈ (head-part (phase ξ)) (½ ·ᴾ liftXor c S) eqP x y)

  -- Where the form vanishes the branches double.

  pairA : ∀ x y → eval (liftXor c S) x y ≡ 0ℤ →
          (zpow (hd x y +ℤ tv x y) +ᴬ zpow (tv x y)) ≐
          (+ 2) ·ᴬ zpow (tv x y)
  pairA x y q0 w = trans
    (Eq.cong₂ _+ℤ_ (zpow-cong {hd x y +ℤ tv x y} {tv x y} same w) refl)
    (twice (zpow (tv x y) w))
    where
    hd0 : pow M ∣ (hd x y - 0ℤ)
    hd0 = Eq.subst (λ u → pow M ∣ (hd x y - u))
      (trans (cong (½ *_) q0) (*-zeroʳ ½)) (head-eval x y)

    shift : ∀ a t → (a +ℤ t) - t ≡ a - 0ℤ
    shift = solve 2 (λ a t → (a :+ t) :- t := a :- con 0ℤ) refl

    same : (+ N) ∣ ((hd x y +ℤ tv x y) - tv x y)
    same = Eq.subst ((+ N) ∣_) (sym (shift (hd x y) (tv x y))) hd0

  -- Where it is 1 they cancel: ζ^(½) = -1.

  pairB : ∀ x y → eval (liftXor c S) x y ≡ 1ℤ →
          (zpow (hd x y +ℤ tv x y) +ᴬ zpow (tv x y)) ≐ 0ᴬ
  pairB x y q1 w = trans
    (Eq.cong₂ _+ℤ_
      (trans (zpow-cong {hd x y +ℤ tv x y} {tv x y +ℤ ½} same w)
             (zpow-anti (tv x y) w))
      refl)
    (+-inverseˡ (zpow (tv x y) w))
    where
    hd½ : pow M ∣ (hd x y - ½)
    hd½ = Eq.subst (λ u → pow M ∣ (hd x y - u))
      (trans (cong (½ *_) q1) (*-identityʳ ½)) (head-eval x y)

    shuffle : ∀ a b t → (a +ℤ t) - (t +ℤ b) ≡ a - b
    shuffle = solve 3 (λ a b t → (a :+ t) :- (t :+ b) := a :- b) refl

    same : (+ N) ∣ ((hd x y +ℤ tv x y) - (tv x y +ℤ ½))
    same = Eq.subst ((+ N) ∣_)
      (sym (shuffle (hd x y) ½ (tv x y))) hd½


  hitsT : Assign n → Assign m → Assign n → Bool
  hitsT x y z = allFin (λ w → eqᵇ (bit (eval (tail-part (out ξ w)) x y)) (z w))

  -- ξ's two branches of y₀, as a single summand over Assign m.

  Fξ : Assign n → Assign n → Assign (suc m) → Amp
  Fξ x z y′ = if hits ξ x y′ z then zpow (eval (phase ξ) x y′) else 0ᴬ

  F : Assign n → Assign n → Assign m → Amp
  F x z y = Fξ x z (extend true y) +ᴬ Fξ x z (extend false y)

  if-pair : ∀ (p : Bool) (a b : Amp) →
            ((if p then a else 0ᴬ) +ᴬ (if p then b else 0ᴬ)) ≐
            (if p then (a +ᴬ b) else 0ᴬ)
  if-pair true  a b _ = refl
  if-pair false a b _ = refl

  if-0ᴬ : ∀ (p : Bool) → (if p then 0ᴬ else 0ᴬ) ≐ 0ᴬ
  if-0ᴬ true  _ = refl
  if-0ᴬ false _ = refl

  ·ᴬ-if : ∀ (p : Bool) (a : Amp) →
          ((+ 2) ·ᴬ (if p then a else 0ᴬ)) ≐
          (if p then ((+ 2) ·ᴬ a) else 0ᴬ)
  ·ᴬ-if true  a _ = refl
  ·ᴬ-if false a _ = *-zeroʳ (+ 2)

  ·ᴬ-map : ∀ (a b : Amp) → a ≐ b → ((+ 2) ·ᴬ a) ≐ ((+ 2) ·ᴬ b)
  ·ᴬ-map a b a≐b w = cong ((+ 2) *_) (a≐b w)

  F-form : ∀ x z y → F x z y ≐
           (if hitsT x y z
            then (zpow (hd x y +ℤ tv x y) +ᴬ zpow (tv x y)) else 0ᴬ)
  F-form x z y w = trans
    (Eq.cong₂ _+ℤ_
      (if-cong (same-hits ξ eqf true x z y)
               (λ w′ → cong (λ u → zpow u w′) (eval-true (phase ξ) x y)) w)
      (if-cong (same-hits ξ eqf false x z y)
               (λ w′ → cong (λ u → zpow u w′) (eval-false (phase ξ) x y)) w))
    (if-pair (hitsT x y z)
             (zpow (hd x y +ℤ tv x y)) (zpow (tv x y)) w)

  F-cancel : ∀ x z u → eval (liftXor c S) x u ≡ 1ℤ → F x z u ≐ 0ᴬ
  F-cancel x z u q1 w = trans
    (trans (F-form x z u w)
             (if-cong {p = hitsT x u z} refl (pairB x u q1) w))
    (if-0ᴬ (hitsT x u z) w)

  twiceᴬ : ∀ (a : Amp) → (a +ᴬ a) ≐ ((+ 2) ·ᴬ a)
  twiceᴬ a w = twice (a w)

  -- Where the form vanishes at every path the branches double, so
  -- every coordinate of the amplitude is even.

  F-double : ∀ x z y → eval (liftXor c S) x y ≡ 0ℤ →
             F x z y ≐
             ((+ 2) ·ᴬ (if hitsT x y z then zpow (tv x y) else 0ᴬ))
  F-double x z y q0 w = trans
    (trans (F-form x z y w)
           (if-cong {p = hitsT x y z} refl (pairA x y q0) w))
    (sym (·ᴬ-if (hitsT x y z) (zpow (tv x y)) w))

  amp-even : (∀ x y → eval (liftXor c S) x y ≡ 0ℤ) → ∀ x z →
             amp ξ x z ≐
             (+ 2) ·ᴬ Σᴮ (λ y → if hitsT x y z then zpow (tv x y) else 0ᴬ)
  amp-even h x z w = trans
    (sym (Σᴮ-+ (λ y → Fξ x z (extend true y))
               (λ y → Fξ x z (extend false y)) w))
    (trans (Σᴮ-cong (λ y → F-double x z y (h x y)) w)
           (sym (·ᴬ-Σᴮ (+ 2)
                  (λ y → if hitsT x y z then zpow (tv x y) else 0ᴬ) w)))

module _ {n k m : ℕ} (ξ : PathSum n k (suc m)) (i : Fin m) (c : Bool)
         (S : Mon n m) (i∈S : y[ i ] ∈ᵐ S)
         (eqP : head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where
  open Cancel ξ c S eqP eqf


  private
    S′ : Mon n m
    S′ = S ∖ᵐ y[ i ]


    -- The value of the form on S ∖ y i, which the reduct substitutes.

    q : Assign n → Assign m → ℤ
    q x y = eval (liftXor c S′) x y

    ⌊no⌋ : ∀ {p} {P : Set p} (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
    ⌊no⌋ (yes p) ¬p = contradiction p ¬p
    ⌊no⌋ (no  _) _  = refl

    ⌊≟⌋-refl : ⌊ i Fin.≟ i ⌋ ≡ true
    ⌊≟⌋-refl with i Fin.≟ i
    ... | yes _ = refl
    ... | no ¬p = contradiction refl ¬p

    setᵗ-i : ∀ (y : Assign m) → setᵗ i y i ≡ true
    setᵗ-i y = cong (λ b → if b then true else y i) ⌊≟⌋-refl

    setᵗ-off : ∀ (y : Assign m) j → ¬ (j ≡ i) → y j ≡ setᵗ i y j
    setᵗ-off y j j≢i =
      sym (cong (λ b → if b then true else y j) (⌊no⌋ (j Fin.≟ i) j≢i))

    novS′ : ∀ γ → y[ i ] ∈ᵐ γ → liftXor c S′ γ ≡ 0ℤ
    novS′ γ v∈γ = liftXor-0 c S′ γ y[ i ] v∈γ (v∉S∖v S y[ i ])

    q-off : ∀ x y → q x y ≡ q x (setᵗ i y)
    q-off x y =
      eval-off (liftXor c S′) i novS′ x y (setᵗ i y) (setᵗ-off y)

    -- The form on S at an assignment, in terms of it.

    Qval : ∀ x y → eval (liftXor c S) x y ≡
           q x y +ℤ ((if y i then 1ℤ else 0ℤ) *
                     (1ℤ - ((+ 2) * q x y)))
    Qval x y = liftXor-split c S y[ i ] i∈S x y

    Q-false : ∀ x y → y i ≡ false → eval (liftXor c S) x y ≡ q x y
    Q-false x y ef = trans (Qval x y) (trans
      (cong (λ b → q x y +ℤ ((if b then 1ℤ else 0ℤ) *
                             (1ℤ - ((+ 2) * q x y)))) ef)
      (trans (cong (q x y +ℤ_) (*-zeroˡ (1ℤ - ((+ 2) * q x y))))
             (+-identityʳ (q x y))))

    Q-true : ∀ x y → y i ≡ true → eval (liftXor c S) x y ≡
             q x y +ℤ (1ℤ - ((+ 2) * q x y))
    Q-true x y et = trans (Qval x y) (trans
      (cong (λ b → q x y +ℤ ((if b then 1ℤ else 0ℤ) *
                             (1ℤ - ((+ 2) * q x y)))) et)
      (cong (q x y +ℤ_) (*-identityˡ (1ℤ - ((+ 2) * q x y)))))

    -- The reduct's polynomials mention no y i, so its summand is
    -- constant along the index the rule eliminates.

    red : PathSum n k m
    red = hh-reduct ξ i c S

    nov-red : ∀ (P : Poly n (suc m)) γ →
              y[ i ] ∈ᵐ γ → subst (tail-part P) y[ i ] c S′ γ ≡ 0ℤ
    nov-red P = subst-0 (tail-part P) y[ i ] c S′ (v∉S∖v S y[ i ])

    phase-off : ∀ x y → eval (phase red) x y ≡ eval (phase red) x (setᵗ i y)
    phase-off x y = eval-off (phase red) i (nov-red (phase ξ))
                             x y (setᵗ i y) (setᵗ-off y)

    hits-off : ∀ x y z → hits red x y z ≡ hits red x (setᵗ i y) z
    hits-off x y z = allFin-cong (λ w →
      cong (λ u → eqᵇ (bit u) (z w))
        (eval-off (out red w) i (nov-red (out ξ w))
                  x y (setᵗ i y) (setᵗ-off y)))

    G : Assign n → Assign n → Assign m → Amp
    G x z y = if hits red x y z then zpow (eval (phase red) x y) else 0ᴬ

    G-off : ∀ x z y → G x z y ≐ G x z (setᵗ i y)
    G-off x z y = if-cong (hits-off x y z)
      (λ w → cong (λ u → zpow u w) (phase-off x y))

    -- Where the assignment satisfies the constraint, substituting
    -- changes no value, so the reduct's summand is ξ's tail.

    kept-phase : ∀ x u → (if u i then 1ℤ else 0ℤ) ≡ q x u →
                 eval (phase red) x u ≡ tv x u
    kept-phase x u cn =
      eval-subst-fixed (tail-part (phase ξ)) y[ i ] c S′ x u cn

    kept-hits : ∀ x u z → (if u i then 1ℤ else 0ℤ) ≡ q x u →
                hits red x u z ≡ hitsT x u z
    kept-hits x u z cn = allFin-cong (λ w →
      cong (λ vv → eqᵇ (bit vv) (z w))
        (eval-subst-fixed (tail-part (out ξ w)) y[ i ] c S′ x u cn))


    G-kept : ∀ x z u → (if u i then 1ℤ else 0ℤ) ≡ q x u →
             G x z u ≐ (if hitsT x u z then zpow (tv x u) else 0ᴬ)
    G-kept x z u cn = if-cong (kept-hits x u z cn)
      (λ w → cong (λ vv → zpow vv w) (kept-phase x u cn))

    F-kept : ∀ x z u → (if u i then 1ℤ else 0ℤ) ≡ q x u →
             eval (liftXor c S) x u ≡ 0ℤ →
             F x z u ≐ ((+ 2) ·ᴬ G x z u)
    F-kept x z u cn q0 w = trans
      (trans (F-form x z u w)
             (if-cong {p = hitsT x u z} refl (pairA x u q0) w))
      (sym (trans (·ᴬ-map (G x z u)
                          (if hitsT x u z then zpow (tv x u) else 0ᴬ)
                          (G-kept x z u cn) w)
                  (·ᴬ-if (hitsT x u z) (zpow (tv x u)) w)))


    -- Of the two assignments differing at i, exactly one satisfies the
    -- constraint: the value of the form on S ∖ y i is the same at both,
    -- and the two give y i opposite values.

    pair-q0 : ∀ x z y → y i ≡ false → q x y ≡ 0ℤ →
              (F x z y +ᴬ F x z (setᵗ i y)) ≐
              (G x z y +ᴬ G x z (setᵗ i y))
    pair-q0 x z y ey q0 w = trans
      (trans (Eq.cong₂ _+ℤ_ (F-kept x z y cn-y Qy0 w)
                            (F-cancel x z (setᵗ i y) Qy′1 w))
             (+-identityʳ (((+ 2) ·ᴬ G x z y) w)))
      (sym (trans (cong (λ u → G x z y w +ℤ u) (sym (G-off x z y w)))
                  (twiceᴬ (G x z y) w)))
      where
      cn-y : (if y i then 1ℤ else 0ℤ) ≡ q x y
      cn-y = trans (cong (λ b → if b then 1ℤ else 0ℤ) ey) (sym q0)

      Qy0 : eval (liftXor c S) x y ≡ 0ℤ
      Qy0 = trans (Q-false x y ey) q0

      Qy′1 : eval (liftXor c S) x (setᵗ i y) ≡ 1ℤ
      Qy′1 = trans (Q-true x (setᵗ i y) (setᵗ-i y))
        (cong (λ u → u +ℤ (1ℤ - ((+ 2) * u))) (trans (sym (q-off x y)) q0))

    pair-q1 : ∀ x z y → y i ≡ false → q x y ≡ 1ℤ →
              (F x z y +ᴬ F x z (setᵗ i y)) ≐
              (G x z y +ᴬ G x z (setᵗ i y))
    pair-q1 x z y ey q1 w = trans
      (trans (Eq.cong₂ _+ℤ_ (F-cancel x z y Qy1 w)
                            (F-kept x z (setᵗ i y) cn-y′ Qy′0 w))
             (+-identityˡ (((+ 2) ·ᴬ G x z (setᵗ i y)) w)))
      (sym (trans (cong (λ u → u +ℤ G x z (setᵗ i y) w) (G-off x z y w))
                  (twiceᴬ (G x z (setᵗ i y)) w)))
      where
      cn-y′ : (if setᵗ i y i then 1ℤ else 0ℤ) ≡ q x (setᵗ i y)
      cn-y′ = trans (cong (λ b → if b then 1ℤ else 0ℤ) (setᵗ-i y))
                     (trans (sym q1) (q-off x y))

      Qy1 : eval (liftXor c S) x y ≡ 1ℤ
      Qy1 = trans (Q-false x y ey) q1

      Qy′0 : eval (liftXor c S) x (setᵗ i y) ≡ 0ℤ
      Qy′0 = trans (Q-true x (setᵗ i y) (setᵗ-i y))
        (cong (λ u → u +ℤ (1ℤ - ((+ 2) * u))) (trans (sym (q-off x y)) q1))

    pair-eq : ∀ x z y →
      (if y i then 0ᴬ else (F x z y +ᴬ F x z (setᵗ i y))) ≐
      (if y i then 0ᴬ else (G x z y +ᴬ G x z (setᵗ i y)))
    pair-eq x z y with y i in ey
    ... | true  = λ _ → refl
    ... | false with liftXor-value c S′ x y
    ...   | inj₁ q0 = pair-q0 x z y ey q0
    ...   | inj₂ q1 = pair-q1 x z y ey q1

    ext-cong : ∀ (b : Bool) (y y′ : Assign m) → (∀ j → y j ≡ y′ j) →
               ∀ j → extend b y j ≡ extend b y′ j
    ext-cong b y y′ agree zero    = refl
    ext-cong b y y′ agree (suc j) = agree j

    Fresp : ∀ x z → Respects (F x z)
    Fresp x z y y′ agree w = Eq.cong₂ _+ℤ_ (br true) (br false)
      where
      br : ∀ b → Fξ x z (extend b y) w ≡ Fξ x z (extend b y′) w
      br b = if-cong
        (allFin-cong (λ u → cong (λ vv → eqᵇ (bit vv) (z u))
          (eval-cong (out ξ u) (λ _ → refl) (ext-cong b y y′ agree))))
        (λ w′ → cong (λ vv → zpow vv w′)
          (eval-cong (phase ξ) (λ _ → refl) (ext-cong b y y′ agree))) w

    Gresp : ∀ x z → Respects (G x z)
    Gresp x z y y′ agree = if-cong
      (allFin-cong (λ u → cong (λ vv → eqᵇ (bit vv) (z u))
        (eval-cong (out red u) (λ _ → refl) agree)))
      (λ w → cong (λ vv → zpow vv w)
        (eval-cong (phase red) (λ _ → refl) agree))

    -- Summing the two branches of y₀, then splitting the remaining sum
    -- at i, matches the reduct pair by pair.

    amp-hh : ∀ x z → amp ξ x z ≐ amp red x z
    amp-hh x z w = trans
      (sym (Σᴮ-+ (λ y → Fξ x z (extend true y))
                 (λ y → Fξ x z (extend false y)) w))
      (trans (Σᴮ-at i (F x z) (Fresp x z) w)
      (trans (Σᴮ-cong (pair-eq x z) w)
             (sym (Σᴮ-at i (G x z) (Gresp x z) w))))

  hh-sound : ξ ≋ hh-reduct ξ i c S
  hh-sound x z = scale-map k (amp-hh x z)


------------------------------------------------------------------------
-- Proposition 3.1

-- Every rule of figure 2 preserves the denotation.

⟶-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ≋ ζ
⟶-sound (elim ξ eqP eqf)         = elim-sound ξ eqP eqf
⟶-sound (ω    ξ c S eqP eqf)     = ω-sound ξ c S eqP eqf
⟶-sound (hh   ξ i c S i∈S eqP eqf) = hh-sound ξ i c S i∈S eqP eqf


------------------------------------------------------------------------
-- Lemma 4.2

-- Where the form on S is 1 the two branches of y₀ cancel, so an input
-- making it 1 at every path kills every amplitude -- which the
-- identity's is not.  Such an input exists whenever the form is not
-- identically 0: all-false does it when the constant is 1, and a
-- single variable of S set to true does it otherwise.

private
  allFin-true : ∀ {j} {f : Fin j → Bool} → (∀ w → f w ≡ true) →
                allFin f ≡ true
  allFin-true {zero}  h = refl
  allFin-true {suc j} h =
    cong₂ _∧_ (h zero) (allFin-true (λ w → h (suc w)))

  eqᵇ-refl : ∀ b → eqᵇ b b ≡ true
  eqᵇ-refl true  = refl
  eqᵇ-refl false = refl

  bit-if : ∀ b → bit (if b then 1ℤ else 0ℤ) ≡ b
  bit-if true  = refl
  bit-if false = refl

  if-0ℤ : ∀ (p : Bool) → (if p then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0ℤ true  = refl
  if-0ℤ false = refl

  dec-false : ∀ {p} {P : Set p} (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
  dec-false (yes q) ¬p = contradiction q ¬p
  dec-false (no  _) _  = refl

  dec-refl : ∀ {j} (u : Fin j) → ⌊ u Fin.≟ u ⌋ ≡ true
  dec-refl u with u Fin.≟ u
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  eval-0ᴾ : ∀ {n m} (x : Assign n) (y : Assign m) →
            eval (0ᴾ {n} {m}) x y ≡ 0ℤ
  eval-0ᴾ {n} {m} x y = trans
    (Σmon-cong {g = λ _ → 0ℤ} (λ γ → if-0ℤ (satᵐ γ x y))) (Σmon-0 {n} {m})

  eval-μ : ∀ {n m} (v : Var n m) (x : Assign n) (y : Assign m) →
           eval (μ v) x y ≡ (if valᵛ v x y then 1ℤ else 0ℤ)
  eval-μ v x y = trans
    (Σmon-cong (λ γ → trans
      (cong (λ b → if satᵐ γ x y then (if b then 1ℤ else 0ℤ) else 0ℤ)
            (⌊≟ᵐ⌋ γ ⟪ v ⟫))
      (if-swap (satᵐ γ x y) (γ ≡ᵐᵇ ⟪ v ⟫) 1ℤ)))
    (trans (Σmon-delta ⟪ v ⟫ (λ γ → if satᵐ γ x y then 1ℤ else 0ℤ))
           (cong (λ b → if b then 1ℤ else 0ℤ) (satᵐ-⟪⟫ v x y)))

  -- The identity path-sum has a single path, of phase 0, and it hits.

  amp-id : ∀ {n} (x : Assign n) → amp idPS x x ≐ zpow 0ℤ
  amp-id {n} x w = trans
    (cong (λ b → (if b then zpow (eval (0ᴾ {n} {0}) x (λ ())) else 0ᴬ) w)
      (allFin-true (λ u → trans
        (cong (λ z → eqᵇ (bit z) (x u)) (eval-μ {n} {0} x[ u ] x (λ ())))
        (trans (cong (λ b → eqᵇ b (x u)) (bit-if (x u))) (eqᵇ-refl (x u))))))
    (cong (λ z → zpow z w) (eval-0ᴾ {n} {0} x (λ ())))

  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    _ = refl
  scale-0ᴬ (suc j) w = trans (√2·-map (scale-0ᴬ j) w) (√2·-0ᴬ w)

  witness′ : ∀ {n m} (c : Bool) (S : Mon n m) → proj₂ S ≡ ⊥ →
             ¬ (c ≡ false × S ≡ 1ᵐ) →
             ∃ λ (x : Assign n) → ∀ (y : Assign m) →
               eval (liftXor c S) x y ≡ 1ℤ
  witness′ {n} {m} c S S-noy nontriv with c
  ... | true  = (λ _ → false) , λ y →
        liftXor-off true S (λ _ → false) y (λ j _ → refl)
          (λ j j∈ → contradiction (Eq.subst (j ∈_) S-noy j∈) ∉⊥)
  ... | false with emptyᵇ (proj₁ S) in eS
  ...   | true  = contradiction (refl , emptyᵐ⇒≡1ᵐ S
          (cong₂ _∧_ eS (trans (cong emptyᵇ S-noy) (emptyᵇ-⊥ {m})))) nontriv
  ...   | false = char , value
    where
    i₀ : Fin n
    i₀ = proj₁ (emptyᵇ-witness (proj₁ S) eS)

    i₀∈ : x[ i₀ ] ∈ᵐ S
    i₀∈ = proj₂ (emptyᵇ-witness (proj₁ S) eS)

    char : Assign n
    char j = ⌊ j Fin.≟ i₀ ⌋

    rest0 : ∀ y → eval (liftXor false (S ∖ᵐ x[ i₀ ])) char y ≡ 0ℤ
    rest0 y = liftXor-off false (S ∖ᵐ x[ i₀ ]) char y
      (λ j j∈ → dec-false (j Fin.≟ i₀)
        (λ eq → ∉∖ (proj₁ S) i₀ (Eq.subst (_∈ (proj₁ S ∖ᶠ i₀)) eq j∈)))
      (λ j j∈ → contradiction (Eq.subst (j ∈_) S-noy j∈) ∉⊥)

    value : ∀ y → eval (liftXor false S) char y ≡ 1ℤ
    value y = trans (liftXor-split false S x[ i₀ ] i₀∈ char y)
      (trans
        (cong (λ u → u +ℤ ((if char i₀ then 1ℤ else 0ℤ) *
                           (1ℤ - ((+ 2) * u)))) (rest0 y))
        (cong (λ b → 0ℤ +ℤ ((if b then 1ℤ else 0ℤ) *
                            (1ℤ - ((+ 2) * 0ℤ)))) (dec-refl i₀)))

module _ {n k m : ℕ} (ξ : PathSum n k (suc m)) (c : Bool) (S : Mon n m)
         (eqP : head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where
  open Cancel ξ c S eqP eqf

  private
    -- An input making the form 1 kills every amplitude of ξ.

    amp-0 : ∀ x → (∀ y → eval (liftXor c S) x y ≡ 1ℤ) →
            ∀ z → amp ξ x z ≐ 0ᴬ
    amp-0 x h z w = trans
      (sym (Σᴮ-+ (λ y → Fξ x z (extend true y))
                 (λ y → Fξ x z (extend false y)) w))
      (trans (Σᴮ-cong (λ y → F-cancel x z y (h y)) w) (Σᴮ-0 {m} w))

    no-id : ∀ x → (∀ y → eval (liftXor c S) x y ≡ 1ℤ) → ¬ (ξ ≋ idPS)
    no-id x h ξ≋id =
      zpow-0≢0ᴬ (λ w → trans (sym (amp-id x w)) (idzero w))
      where
      idzero : amp idPS x x ≐ 0ᴬ
      idzero = scale-injective k (amp idPS x x) 0ᴬ
        (λ w → trans (sym (ξ≋id x x w))
                     (trans (amp-0 x h x w) (sym (scale-0ᴬ k w))))


  interference-lemma : proj₂ S ≡ ⊥ → ¬ (c ≡ false × S ≡ 1ᵐ) → ¬ (ξ ≋ idPS)
  interference-lemma S-noy nontriv =
    no-id (proj₁ w) (proj₂ w)
    where
    w = witness′ c S S-noy nontriv

  -- The undersized case of lemma 4.3 for [Elim]: if the form vanishes
  -- identically the branches double, and an amplitude every
  -- coordinate of which is even is not the identity's.

  undersized-elim : (∀ x y → eval (liftXor c S) x y ≡ 0ℤ) → k < 2 →
                    ¬ (ξ ≋ idPS)
  undersized-elim h k<2 ξ≋id = 2·≢scale-zpow0 B k k<2 (λ w →
    trans (sym (amp-even h x₀ x₀ w))
          (trans (ξ≋id x₀ x₀ w) (scale-map k (amp-id x₀) w)))
    where
    x₀ : Assign n
    x₀ _ = false

    B : Amp
    B = Σᴮ (λ y → if hitsT x₀ y x₀ then zpow (tv x₀ y) else 0ᴬ)


------------------------------------------------------------------------
-- The denotation as a semantics

-- Every field of the interface is now proved, so section 4.3 holds of
-- this denotation rather than of a hypothetical one.

semantics : Semantics
Semantics._≋_          semantics = _≋_
Semantics.≋-refl  semantics {ξ = a} = ≋-refl {ξ = a}
Semantics.≋-sym   semantics {ξ = a} {ζ = b} = ≋-sym {ξ = a} {ζ = b}
Semantics.≋-trans semantics {ξ = a} {ζ = b} {χ = d} =
  ≋-trans {ξ = a} {ζ = b} {χ = d}
Semantics.⟶-sound semantics {ξ = a} {ζ = b} = ⟶-sound {ξ = a} {ζ = b}
Semantics.interference semantics = interference-lemma
