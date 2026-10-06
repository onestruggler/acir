------------------------------------------------------------------------
-- Presentations of groups
--
-- When restriction and the rules of figure 2 are both stuck (Amy, QPL
-- 2018, sections 4 and 4.1)
--
-- PathSum.Restrict interleaves the isometry restriction of section 4.1
-- with the rules of figure 2 (chains _⇝*_).  This module gives
-- sufficient conditions under which no such chain from a path-sum
-- reaches one without path variables -- the situation in which the
-- syntactic verdict of corollary 4.4 is never available and only
-- expansion decides -- and the tools to check them on a closed
-- path-sum cheaply.
--
-- * Dead ρ: ρ is irreducible under figure 2 and every output of ρ
--   reads its input on every path (Solved).  A restriction step at a
--   wire needs the discarded path to miss that wire's input, which a
--   solved wire never does, so from a dead path-sum with a path
--   variable no chain at all leaves it (dead-stuck).
--
-- * If every restriction step from ξ leads to a dead path-sum and ξ is
--   irreducible itself, no chain from ξ reaches a path-sum without path
--   variables (stuck-after-one).
--
-- * Which steps a path-sum allows (only-step): if every wire but w₀ is
--   solved and w₀ reads the newest path variable y₀ on every path, a
--   restriction step must be at w₀ and y₀ (any other variable leaves
--   w₀'s value unchanged between the kept and the discarded path).
--   Its reduct is then unique coefficient by coefficient
--   (PathSum.Restrict.Pivot.restricts-unique), so it suffices to know
--   one: if that one is dead by PathSum.Full.Obstruction's certificate,
--   every one is (any-step-dead).  The certificate reads four phase
--   coefficients modulo powers of 2 dividing 2^M, so it survives a
--   change of the phase by multiples of 2^M (Obstructed-≈), and solved
--   outputs survive a change by even coefficients (Solved-≈).
--
-- The instance is PathSum.Examples.IncompleteRestrict, the identity of
-- section 4 under its restriction.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Restrict.Stuck (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; false; not)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset using (⊥; inside)
open import Data.Integer.Base using (ℤ; +_; _-_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-refl; ∣-trans; ∣m∣n⇒∣m-n)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_∸_)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (_∷_; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Denotation M₀ using (Assign; outBit)
open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Full.Obstruction M using
  (coef₀₁; Necessary; Obstructed; obstructed⇒irreducible)
open import PathSum.Order M using (pow; pow-∣)
open import PathSum.Polynomial using (Poly; _≈[_]_; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Parity using (≡-odd)
open import PathSum.Polynomial.Properties using (eval-≈)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using (front; frontᴾ; insertᵃ)
open import PathSum.Restrict M₀ using
  (Solved; Restricts; _⇝*_; restrict; rule; _◅⇝_; step)
open import PathSum.Restrict.Pivot M₀ using (restricts-unique)

open +-*-Solver using (solve; _:-_; _:=_)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Dead path-sums

-- Irreducible under figure 2, and every output solved.

Dead : PathSum n k m → Set
Dead {n} ρ = Irreducibleᶠ ρ × (∀ (w : Fin n) → Solved ρ w)

private
  not-≢ : ∀ b → not b ≢ b
  not-≢ Bool.false ()
  not-≢ Bool.true  ()

  false₀ : ∀ {j} → Assign j
  false₀ _ = false

-- A solved wire never misses its input, so no restriction step is at
-- it.

solved-no-step : {ξ : PathSum n k (suc m)} {w : Fin n} {j : Fin (suc m)}
                 {ρ : PathSum n k m} → Solved ξ w → ¬ Restricts ξ w j ρ
solved-no-step {w = w} {j} solved r = not-≢ (false₀ w)
  (trans (sym (Restricts.miss r false₀ false₀))
         (solved false₀ (insertᵃ j (not (Restricts.keep r false₀ false₀))
                                  false₀)))

-- From a dead path-sum with a path variable, no chain leaves.

dead-stuck : (ρ : PathSum n k (suc m)) → Dead ρ →
             ∀ {k′} {ζ : PathSum n k′ 0} → ¬ (ρ ⇝* ζ)
dead-stuck ρ (irr , solved) (rule s ◅⇝ _)                = irr s
dead-stuck ρ (irr , solved) (restrict (step w j r) ◅⇝ _) =
  solved-no-step (solved w) r

-- If ξ is irreducible and every restriction step from it is dead, no
-- chain from ξ reaches a path-sum without path variables.

stuck-after-one :
  (ξ : PathSum n k (suc (suc m))) → Irreducibleᶠ ξ →
  (∀ {w j} {ρ : PathSum n k (suc m)} → Restricts ξ w j ρ → Dead ρ) →
  ∀ {k′} {ζ : PathSum n k′ 0} → ¬ (ξ ⇝* ζ)
stuck-after-one ξ irr dead (rule s ◅⇝ _)                   = irr s
stuck-after-one ξ irr dead (restrict (step w j r) ◅⇝ rest) =
  dead-stuck _ (dead r) rest


------------------------------------------------------------------------
-- Robustness of the certificate and of solved outputs

private
  -- p ∣ a′ moves to a when 2^M divides a′ − a and p divides 2^M.

  move : ∀ {p a a′} → p ∣ pow M → pow M ∣ (a′ - a) → p ∣ a′ → p ∣ a
  move {p} {a} {a′} p∣N d p∣a′ =
    subst (p ∣_) (back a a′) (∣m∣n⇒∣m-n p∣a′ (∣-trans p∣N d))
    where
    back : ∀ a a′ → a′ - (a′ - a) ≡ a
    back = solve 2 (λ a a′ → a′ :- (a′ :- a) := a) refl

  move½ : ∀ {a a′} → pow M ∣ (a′ - a) → pow M ∣ (a′ - ½) → pow M ∣ (a - ½)
  move½ {a} {a′} d h = subst (pow M ∣_) (back a a′ ½) (∣m∣n⇒∣m-n h d)
    where
    back : ∀ a a′ h → (a′ - h) - (a′ - a) ≡ a - h
    back = solve 3 (λ a a′ h → (a′ :- h) :- (a′ :- a) := a :- h) refl

  ¼∣N : pow (M ∸ 2) ∣ pow M
  ¼∣N = pow-∣ (m∸n≤m M 2)

  ½∣N : pow (M ∸ 1) ∣ pow M
  ½∣N = pow-∣ (m∸n≤m M 1)

  frontᴾ-≈ : (j : Fin (suc m)) {P Q : Poly n (suc m)} {c : ℤ} →
             P ≈[ c ] Q → frontᴾ j P ≈[ c ] frontᴾ j Q
  frontᴾ-≈ j h (α , b ∷ s) = h (α , insertAt s j b)

  -- The four coefficients, moved from χ′ to χ.

  Necessary-≈ : (i : Fin n) (χ χ′ : PathSum n k (suc (suc m))) →
                phase χ′ ≈[ pow M ] phase χ →
                Necessary i χ′ → Necessary i χ
  Necessary-≈ i χ χ′ h (d₀ , inj₁ dˣ) =
    move ¼∣N (h _) d₀ , inj₁ (move ½∣N (h _) dˣ)
  Necessary-≈ i χ χ′ h (d₀ , inj₂ (d₀₁ , d₁)) =
    move ¼∣N (h _) d₀ ,
    inj₂ (move½ {a = coef₀₁ χ} {a′ = coef₀₁ χ′}
                (h (⊥ , inside ∷ inside ∷ ⊥)) d₀₁ ,
          move ¼∣N (h _) d₁)

-- The certificate holds of every path-sum whose phase agrees with that
-- of a certified one modulo 2^M.

Obstructed-≈ : (i : Fin n) (ρ ρ′ : PathSum n k (suc (suc m))) →
               phase ρ′ ≈[ pow M ] phase ρ → Obstructed i ρ → Obstructed i ρ′
Obstructed-≈ i ρ ρ′ h obs j j′ nec′ =
  obs j j′ (Necessary-≈ i (front j′ (front j ρ)) (front j′ (front j ρ′))
                        (frontᴾ-≈ j′ (frontᴾ-≈ j h)) nec′)

-- A solved output stays solved when its coefficients change by even
-- numbers.

Solved-≈ : (ρ ρ′ : PathSum n k m) (w : Fin n) →
           out ρ′ w ≈[ + 2 ] out ρ w → Solved ρ w → Solved ρ′ w
Solved-≈ ρ ρ′ w h solved x g = trans
  (≡-odd (eval (out ρ′ w) x g) (eval (out ρ w) x g)
         (eval-≈ (out ρ′ w) (out ρ w) h x g))
  (solved x g)


------------------------------------------------------------------------
-- Which restriction steps a path-sum allows

private
  -- A step at w₀ eliminates y₀: at any other variable the kept and the
  -- discarded path read the same value on w₀, which cannot be both x_w₀
  -- and its negation.

  at-y₀ : (ξ : PathSum n k (suc m)) (w₀ : Fin n) →
          (∀ x y → outBit ξ x y w₀ ≡ y zero) →
          (j : Fin (suc m)) {ρ : PathSum n k m} → Restricts ξ w₀ j ρ →
          j ≡ zero
  at-y₀           ξ w₀ reads zero     r = refl
  at-y₀ {m = suc m} ξ w₀ reads (suc j) r = contradiction
    (trans e₁ (sym e₂)) (not-≢ (false₀ w₀))
    where
    open Restricts r

    b : Bool
    b = keep false₀ false₀

    e₁ : not (false₀ w₀) ≡ false
    e₁ = trans (sym (miss false₀ false₀))
               (reads false₀ (insertᵃ (suc j) (not b) false₀))

    e₂ : false₀ w₀ ≡ false
    e₂ = trans (sym (solves false₀ false₀))
               (trans (outs false₀ false₀ w₀)
                      (reads false₀ (insertᵃ (suc j) b false₀)))

-- Every wire but w₀ is solved, and w₀ reads the newest path variable on
-- every path: a step must be at w₀ and that variable.

only-step : (ξ : PathSum n k (suc m)) (w₀ : Fin n) →
            (∀ v → v ≢ w₀ → Solved ξ v) →
            (∀ x y → outBit ξ x y w₀ ≡ y zero) →
            ∀ {w j} {ρ : PathSum n k m} → Restricts ξ w j ρ →
            (w ≡ w₀) × (j ≡ zero)
only-step ξ w₀ others reads {w} {j} r with w ≟ w₀
... | no w≢w₀  = contradiction r (solved-no-step (others w w≢w₀))
... | yes refl = refl , at-y₀ ξ w reads j r

-- So when one step from ξ is known, and certified dead, every step is
-- dead: its reduct agrees with the known one coefficient by
-- coefficient.

any-step-dead :
  (ξ : PathSum n k (suc (suc (suc m)))) (w₀ : Fin n) →
  (∀ v → v ≢ w₀ → Solved ξ v) → (∀ x y → outBit ξ x y w₀ ≡ y zero) →
  {ρ₀ : PathSum n k (suc (suc m))} → Restricts ξ w₀ zero ρ₀ →
  (i : Fin n) → Obstructed i ρ₀ → (∀ w → Solved ρ₀ w) →
  ∀ {w j} {ρ : PathSum n k (suc (suc m))} → Restricts ξ w j ρ → Dead ρ
any-step-dead ξ w₀ others reads {ρ₀} r₀ i obs solved₀ {ρ = ρ} r
  with only-step ξ w₀ others reads r
... | refl , refl =
  obstructed⇒irreducible i ρ (Obstructed-≈ i ρ₀ ρ (proj₁ same) obs) ,
  (λ v → Solved-≈ ρ₀ ρ v (proj₂ same v) (solved₀ v))
  where
  same = restricts-unique r r₀
