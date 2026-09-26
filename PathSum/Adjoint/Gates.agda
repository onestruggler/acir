------------------------------------------------------------------------
-- Presentations of groups
--
-- Inverting and conjugating the gate matrices (Amy, QPL 2018,
-- sections 2.2 and 3)
--
-- Both gate sets of the development act on columns by the three kinds
-- of unnormalised matrix of PathSum.Unitarity.Gates: a Hadamard hadᴬ w,
-- a diagonal phase phaseᴬ e (S, CZ, R_k, R_k†) and a controlled NOT
-- cnotᴬ c t.  This module proves, once for both gate sets, the facts
-- about them that inverting a circuit rests on.
--
-- Inverses.  H H = 2, CNOT CNOT = 1, and the phase ζ^(-e) undoes the
-- phase ζ^e, as unnormalised matrices (had-had, cnot-cnot,
-- phase-cancel): a Hadamard's pair of new entries a + b , a - b goes
-- back to 2a , 2b, the CNOT's permutation is its own inverse, and
-- rotations compose by adding exponents.  Together with S⁴ = 1 and
-- CZ² = 1 (PathSum.Miter) these are the cancellations of section 3's
-- miter.  No unitarity is used.
--
-- Linearity.  Each kind of gate builds a new entry from old ones by
-- sums and rotations only, so it commutes with every linear map of
-- PathSum.AmpLinear applied entry by entry (had-linear, phase-linear,
-- cnot-linear) -- in particular with the normalisations √2^k and 2^k.
--
-- Conjugation.  Complex conjugation, PathSum.Ring's conj (ζ ↦ ζ⁻¹),
-- passes through each kind of matrix, turning it into the matrix of the
-- inverse gate: a phase ζ^e into ζ^(-e) (conj-phase), a CNOT into
-- itself (conj-cnot), and a Hadamard into itself (conj-had), since its
-- sign (-1)^(z_w) = ζ^(½ z_w) is real (rot-½).  For S, whose inverse
-- {H , S , CZ} spells S S S, the phase ζ^(¼ z_w) conjugated is its cube
-- (rot-¼³), as ζ^(¼·4) = 1.  And the basis columns are real (conj-δ).
-- These are what make the path-sum of C† the conjugate transpose of
-- that of C (PathSum.Adjoint.Conjugate, PathSum.CRK.Conjugate).
--
-- Exponents of rotations are changed only through rot-exp, with both
-- exponents written out, and a gate's exponent is abstracted as e with
-- an equation e ≡ ½ * [ b ]ᶻ before the case split on the bit b:
-- ½ * [ true ]ᶻ is not definitionally ½.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Adjoint.Gates (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-inverseˡ; +-inverseʳ; *-identityʳ; *-zeroʳ;
   neg-involutive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (Linear)
open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-self; same)
open import PathSum.CircuitSemantics M₀ using (Column; δ; sign-0; sign-1)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _+ᴬ_; _-ᴬ_; -ᴬ_; _·ᴬ_; zpow; rot; rot-map; rot-exp;
   rot-comp; rot-0; rot-anti; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Order M using (pow-suc)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Ring M₀ using
  (conj; conj-+ᴬ; conj-rot; conj-zpow; conj-0ᴬ)
open import PathSum.Unitarity.Gates M₀ using
  (hadᴬ; phaseᴬ; cnotᴬ; had-0; had-1; cnot-involutive)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Rotations by the phases of the gates

-- ζ^½ = -1 and ζ^(-½) = -1: ½ is the exponent H of ζ^H = -1
-- (Cyclotomic's H, imported as rank).

rot-½⁺ : (a : Amp) → rot ½ a ≐ -ᴬ a
rot-½⁺ a i =
  trans (rot-exp {½} {0ℤ + (+ rank)} a (sym (+-identityˡ ½)) i)
        (trans (rot-anti 0ℤ a i) (cong -_ (rot-0 a i)))

rot-½⁻ : (a : Amp) → rot (- ½) a ≐ -ᴬ a
rot-½⁻ a i =
  trans (sym (neg-involutive (rot (- ½) a i))) (cong -_ back)
  where
  back : - rot (- ½) a i ≡ a i
  back = trans (sym (rot-anti (- ½) a i))
    (trans (rot-exp { - ½ + (+ rank)} {0ℤ} a (+-inverseˡ ½) i)
           (rot-0 a i))

-- So ζ^(½ b) is real, ±1: conjugation leaves it alone.  (The sign of
-- a Hadamard, and the phase of CZ.)

rot-½ : (e : ℤ) (b : Bool) → e ≡ ½ * [ b ]ᶻ → (a : Amp) →
        rot e a ≐ rot (- e) a
rot-½ e false eq a i =
  trans (rot-exp {e} {0ℤ} a e₀ i)
        (sym (rot-exp { - e} {0ℤ} a (cong -_ e₀) i))
  where
  e₀ : e ≡ 0ℤ
  e₀ = trans eq (*-zeroʳ ½)
rot-½ e true  eq a i =
  trans (rot-exp {e} {½} a e₁ i)
    (trans (rot-½⁺ a i)
      (sym (trans (rot-exp { - e} { - ½} a (cong -_ e₁) i) (rot-½⁻ a i))))
  where
  e₁ : e ≡ ½
  e₁ = trans eq (*-identityʳ ½)

-- ζ^(¼ b) has order dividing 4: four rotations by it are none.  At a
-- bit 0 every rotation is by 0; at 1 they add up to 4 · ¼ = 2H = N,
-- two negations.

private
  ¼+¼ : ¼ + ¼ ≡ ½
  ¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))
    where
    double : ∀ u → u + u ≡ u * (+ 2)
    double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  four-¼ : ∀ q → q ≡ ¼ → q + (q + (q + q)) ≡ (0ℤ + ½) + ½
  four-¼ q eq =
    trans (cong (λ u → u + (u + (u + u))) eq)
      (trans (regroup ¼)
        (trans (cong (λ u → u + u) ¼+¼)
               (cong (λ u → u + ½) (sym (+-identityˡ ½)))))
    where
    regroup : ∀ u → u + (u + (u + u)) ≡ (u + u) + (u + u)
    regroup = solve 1 (λ u → u :+ (u :+ (u :+ u)) := (u :+ u) :+ (u :+ u))
                refl

  rot-N : (a : Amp) → rot ((0ℤ + (+ rank)) + (+ rank)) a ≐ a
  rot-N a i =
    trans (rot-anti (0ℤ + (+ rank)) a i)
      (trans (cong -_ (rot-anti 0ℤ a i))
        (trans (neg-involutive (rot 0ℤ a i)) (rot-0 a i)))

  cycle⁴ : (e : ℤ) (b : Bool) → e ≡ ¼ * [ b ]ᶻ → (a : Amp) →
           rot (e + (e + (e + e))) a ≐ a
  cycle⁴ e false eq a i =
    trans (rot-exp {e + (e + (e + e))} {0ℤ} a
                   (cong (λ u → u + (u + (u + u)))
                         (trans eq (*-zeroʳ ¼))) i)
          (rot-0 a i)
  cycle⁴ e true  eq a i =
    trans (rot-exp {e + (e + (e + e))} {(0ℤ + (+ rank)) + (+ rank)} a
                   (four-¼ e (trans eq (*-identityʳ ¼))) i)
          (rot-N a i)

  fold⁴ : (e : ℤ) (a : Amp) →
          rot e (rot e (rot e (rot e a))) ≐ rot (e + (e + (e + e))) a
  fold⁴ e a i =
    trans (rot-map e (rot-map e (rot-comp e e a)) i)
      (trans (rot-map e (rot-comp e (e + e) a) i)
             (rot-comp e (e + (e + e)) a i))

-- A rotation undone by the opposite one, on either side.

rot-cancelˡ : (e : ℤ) (a : Amp) → rot (- e) (rot e a) ≐ a
rot-cancelˡ e a i =
  trans (rot-comp (- e) e a i)
    (trans (rot-exp { - e + e} {0ℤ} a (+-inverseˡ e) i) (rot-0 a i))

rot-cancelʳ : (e : ℤ) (a : Amp) → rot e (rot (- e) a) ≐ a
rot-cancelʳ e a i =
  trans (rot-comp e (- e) a i)
    (trans (rot-exp {e + - e} {0ℤ} a (+-inverseʳ e) i) (rot-0 a i))

-- So ζ^(¼ b) conjugated, ζ^(-¼ b), is its cube: the phase of S S S.

rot-¼³ : (e : ℤ) (b : Bool) → e ≡ ¼ * [ b ]ᶻ → (a : Amp) →
         rot e (rot e (rot e a)) ≐ rot (- e) a
rot-¼³ e b eq a i =
  trans (rot-map e (rot-map e (rot-map e
           (λ j → sym (rot-cancelʳ e a j)))) i)
    (trans (fold⁴ e (rot (- e) a) i) (cycle⁴ e b eq (rot (- e) a) i))


------------------------------------------------------------------------
-- H H = 2

-- The inner Hadamard sends the entries a and b at z[w≔0] and z[w≔1]
-- to a + b and a - b there (PathSum.Unitarity.Gates's had-0, had-1),
-- and the outer one adds the two, or subtracts them, according as z_w
-- is 0 or 1: 2a or 2b, twice the old entry at z.

private
  sum-diff : ∀ p q → (p + q) + (p - q) ≡ (+ 2) * p
  sum-diff = solve 2 (λ p q → (p :+ q) :+ (p :- q) := con (+ 2) :* p) refl

  diff-diff : ∀ p q → (p + q) - (p - q) ≡ (+ 2) * q
  diff-diff = solve 2 (λ p q → (p :+ q) :- (p :- q) := con (+ 2) :* q)
                refl

had-had : (w : Fin n) (ψ : Column n) → Respects ψ →
          ∀ z → hadᴬ w (hadᴬ w ψ) z ≐ (+ 2) ·ᴬ ψ z
had-had w ψ resp z = at (z w) refl
  where
  in₀ = had-0 w ψ resp z
  in₁ = had-1 w ψ resp z

  -- Writing z's own value on w back gives z.

  back : (b : Bool) → z w ≡ b → ψ (z [ w ≔ b ]) ≐ ψ z
  back b eq = resp (z [ w ≔ b ]) z (λ j →
    trans (cong (λ u → (z [ w ≔ u ]) j) (sym eq)) (≔-self z w j))

  at : (b : Bool) → z w ≡ b →
       hadᴬ w (hadᴬ w ψ) z ≐ (+ 2) ·ᴬ ψ z
  at false eq i =
    trans (sign-0 (hadᴬ w ψ (z [ w ≔ false ]))
                  (ψ (z [ w ≔ false ]) +ᴬ ψ (z [ w ≔ true ]))
                  (hadᴬ w ψ (z [ w ≔ true ]))
                  (ψ (z [ w ≔ false ]) -ᴬ ψ (z [ w ≔ true ]))
                  (½ * [ z w ]ᶻ) in₀
                  (trans (cong (λ b → ½ * [ b ]ᶻ) eq) (*-zeroʳ ½)) in₁ i)
      (trans (sum-diff (ψ (z [ w ≔ false ]) i) (ψ (z [ w ≔ true ]) i))
             (cong (λ u → (+ 2) * u) (back false eq i)))
  at true  eq i =
    trans (sign-1 (hadᴬ w ψ (z [ w ≔ false ]))
                  (ψ (z [ w ≔ false ]) +ᴬ ψ (z [ w ≔ true ]))
                  (hadᴬ w ψ (z [ w ≔ true ]))
                  (ψ (z [ w ≔ false ]) -ᴬ ψ (z [ w ≔ true ]))
                  (½ * [ z w ]ᶻ) in₀
                  (trans (cong (λ b → ½ * [ b ]ᶻ) eq)
                         (trans (*-identityʳ ½) (sym (+-identityˡ ½))))
                  in₁ i)
      (trans (diff-diff (ψ (z [ w ≔ false ]) i) (ψ (z [ w ≔ true ]) i))
             (cong (λ u → (+ 2) * u) (back true eq i)))


------------------------------------------------------------------------
-- CNOT CNOT = 1, and a phase undone by its negation

cnot-cnot : (c t : Fin n) → c ≢ t → (ψ : Column n) → Respects ψ →
            ∀ z → cnotᴬ c t (cnotᴬ c t ψ) z ≐ ψ z
cnot-cnot c t p ψ resp z = resp _ z (cnot-involutive c t p z)

phase-cancel : (e : Assign n → ℤ) (ψ : Column n) →
               ∀ z → phaseᴬ (λ u → - e u) (phaseᴬ e ψ) z ≐ ψ z
phase-cancel e ψ z = rot-cancelˡ (e z) (ψ z)

phase-cancel⁻ : (e : Assign n → ℤ) (ψ : Column n) →
                ∀ z → phaseᴬ e (phaseᴬ (λ u → - e u) ψ) z ≐ ψ z
phase-cancel⁻ e ψ z = rot-cancelʳ (e z) (ψ z)


------------------------------------------------------------------------
-- The gate matrices commute with linear maps

-- A gate builds each new entry from old ones by sums and rotations, so
-- a linear map applied to every entry before the gate may as well be
-- applied after it.

had-linear : ∀ {f} → Linear f → (w : Fin n) (ψ : Column n) →
             ∀ z → hadᴬ w (λ u → f (ψ u)) z ≐ f (hadᴬ w ψ z)
had-linear {f = f} lin w ψ z i =
  trans (cong (λ u → f (ψ (z [ w ≔ false ])) i + u)
              (sym (Linear.map-rot lin (½ * [ z w ]ᶻ)
                                   (ψ (z [ w ≔ true ])) i)))
        (sym (Linear.map-+ᴬ lin (ψ (z [ w ≔ false ]))
               (rot (½ * [ z w ]ᶻ) (ψ (z [ w ≔ true ]))) i))

phase-linear : ∀ {f} → Linear f → (e : Assign n → ℤ) (ψ : Column n) →
               ∀ z → phaseᴬ e (λ u → f (ψ u)) z ≐ f (phaseᴬ e ψ z)
phase-linear lin e ψ z i = sym (Linear.map-rot lin (e z) (ψ z) i)

cnot-linear : ∀ {f} → Linear f → (c t : Fin n) (ψ : Column n) →
              ∀ z → cnotᴬ c t (λ u → f (ψ u)) z ≐ f (cnotᴬ c t ψ z)
cnot-linear lin c t ψ z _ = refl


------------------------------------------------------------------------
-- Conjugating the gate matrices

-- A phase ζ^e, conjugated, is ζ^(-e); read the other way, ζ^(-e)
-- conjugated is ζ^e.

conj-phase : (e : Assign n → ℤ) (ψ : Column n) →
             ∀ z → conj (phaseᴬ e ψ z) ≐
                   phaseᴬ (λ u → - e u) (λ u → conj (ψ u)) z
conj-phase e ψ z = conj-rot (e z) (ψ z)

conj-phase⁻ : (e : Assign n → ℤ) (ψ : Column n) →
              ∀ z → conj (phaseᴬ (λ u → - e u) ψ z) ≐
                    phaseᴬ e (λ u → conj (ψ u)) z
conj-phase⁻ e ψ z i =
  trans (conj-rot (- e z) (ψ z) i)
        (rot-exp { - (- e z)} {e z} (conj (ψ z)) (neg-involutive (e z)) i)

-- A CNOT only moves entries.

conj-cnot : (c t : Fin n) (ψ : Column n) →
            ∀ z → conj (cnotᴬ c t ψ z) ≐ cnotᴬ c t (λ u → conj (ψ u)) z
conj-cnot c t ψ z _ = refl

-- A Hadamard's sign is real, so conjugation passes through it.

conj-had : (w : Fin n) (ψ : Column n) →
           ∀ z → conj (hadᴬ w ψ z) ≐ hadᴬ w (λ u → conj (ψ u)) z
conj-had w ψ z i =
  trans (conj-+ᴬ (ψ (z [ w ≔ false ])) (rot e (ψ (z [ w ≔ true ]))) i)
    (cong (λ u → conj (ψ (z [ w ≔ false ])) i + u)
      (trans (conj-rot e (ψ (z [ w ≔ true ])) i)
             (sym (rot-½ e (z w) refl (conj (ψ (z [ w ≔ true ]))) i))))
  where
  e = ½ * [ z w ]ᶻ

-- The basis columns are real.

conj-δ : (x : Assign n) → ∀ z → conj (δ x z) ≐ δ x z
conj-δ x z = real (same x z)
  where
  real : (b : Bool) → conj (if b then zpow 0ℤ else 0ᴬ) ≐
                      (if b then zpow 0ℤ else 0ᴬ)
  real true  = conj-zpow 0ℤ
  real false = conj-0ᴬ
