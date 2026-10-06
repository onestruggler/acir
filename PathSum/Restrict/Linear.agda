------------------------------------------------------------------------
-- Presentations of groups
--
-- Gaussian elimination is a chain of restriction steps (Amy, QPL 2018,
-- section 4.1 and the proof of corollary 4.4)
--
-- PathSum.Gauss reifies the isometry restriction of a path-sum whose
-- outputs are affine forms (a PathSum.CRK.Circuit state) by Gaussian
-- elimination, each step substituting y_j ← f_w ⊕ x_w ⊕ y_j for a
-- pivot y_j of the form f_w on wire w.  Read through PathSum.Restrict,
-- each such step is a restriction step in the general sense, at that
-- wire and variable (gauss-restricts): the kept path is Gauss's pick,
-- the other one misses x_w (Gauss.miss-step), and along the kept one
-- the outputs and the phase are the reduct's (val-step, eval-step).
-- So the elimination, run to the end, is a chain of restriction steps
-- (eliminate) ending where no output mentions a path variable; there
-- every output is x_w or misses x_w at some input
-- (PathSum.Gauss.Forms.verdict), and PathSum.Restrict's theorems give
-- Gauss's own verdict back (linear-verdict): ¬ ξ ≋ |x⟩ ↦ |x⟩, or, for a
-- well-formed ξ, ξ ≋ |x⟩ ↦ |x⟩ exactly when the end is.  That is the
-- linear case of the general restriction, whose "ignored"
-- restrictions never occur here: every output ends up path-free.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Restrict.Linear (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; not)
open import Data.Bool.Properties using (not-involutive)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (_-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; idPS)
open import PathSum.CRK.Amp M₀ using (toPS; outBit-liftᴸ)
open import PathSum.CRK.Circuit M using (State; poly; sig)
open import PathSum.Denotation M₀ using (Assign; outBit; _≋_)
open import PathSum.Gauss.Forms using
  (coefʸ; Pivot; pivot; none; pivot?; verdict; some-or-all)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.Linear using (valᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reorder using (insertᵃ)
open import PathSum.Restrict M₀ using
  (Solved; Restricts; _↝_; step; _↝*_; εʳ; _◅ʳ_; ↝*⇒⇝*;
   restriction-solved; restriction-refutes)

import PathSum.Gauss

private
  module G = PathSum.Gauss M₀

  variable
    n m k : ℕ


------------------------------------------------------------------------
-- One step

gauss-restricts : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
                  coefʸ (sig st w) j ≡ true →
                  Restricts (toPS {k = k} st) w j (toPS {k = k} (G.step st w j))
gauss-restricts {k = k} st w j piv = record
  { keep   = G.pick st w j
  ; miss   = λ x g → trans
      (outBit-liftᴸ (toPS {k = k} st) x (insertᵃ j (not (G.pick st w j x g)) g)
                    w (sig st w) refl)
      (G.miss-step st w j piv x g (not (G.pick st w j x g))
                   (sym (not-involutive (G.pick st w j x g))))
  ; outs   = λ x g v → trans
      (outBit-liftᴸ (toPS {k = k} (G.step st w j)) x g v
                    (sig (G.step st w j) v) refl)
      (trans (G.val-step st w j piv v x g (G.pick st w j x g) refl)
             (sym (outBit-liftᴸ (toPS {k = k} st) x
                    (insertᵃ j (G.pick st w j x g) g) v (sig st v) refl)))
  ; solves = λ x g → trans
      (outBit-liftᴸ (toPS {k = k} (G.step st w j)) x g w
                    (sig (G.step st w j) w) refl)
      (G.step-solves st w j piv x g)
  ; phase≡ = λ x g → subst (pow M ∣_)
      (sym (trans (cong (λ e → e - eval (poly st) x
                                  (insertᵃ j (G.pick st w j x g) g))
                        (G.eval-step st w j piv x g (G.pick st w j x g) refl))
                  (+-inverseʳ (eval (poly st) x
                                (insertᵃ j (G.pick st w j x g) g)))))
      i∣0
  }


------------------------------------------------------------------------
-- The elimination as a chain

-- Run to the end: no output mentions a path variable.

record Eliminated {n m : ℕ} (st : State n m) (k : ℕ) : Set where
  field
    left  : ℕ
    final : State n left
    chain : toPS {k = k} st ↝* toPS {k = k} final
    free  : ∀ w j → coefʸ (sig final w) j ≡ false

mutual
  eliminate : (st : State n m) → Eliminated st k
  eliminate st = eliminate-by st (pivot? (sig st))

  eliminate-by : (st : State n m) → Pivot (sig st) → Eliminated st k
  eliminate-by {m = zero}          st (pivot w () _)
  eliminate-by {m = suc m} {k = k} st (pivot w j piv) = record
    { left  = Eliminated.left rest
    ; final = Eliminated.final rest
    ; chain = step w j (gauss-restricts {k = k} st w j piv) ◅ʳ
              Eliminated.chain rest
    ; free  = Eliminated.free rest
    }
    where
    rest : Eliminated (G.step st w j) k
    rest = eliminate (G.step st w j)
  eliminate-by st (none free) = record
    { left = _ ; final = st ; chain = εʳ ; free = free }


------------------------------------------------------------------------
-- The verdict

-- At the end every output is x_w, or misses x_w on every path from
-- some input.

settled : (st : State n m) → (∀ w j → coefʸ (sig st w) j ≡ false) →
          (∀ w → Solved (toPS {k = k} st) w) ⊎
          (∃ λ w → ∃ λ (x : Assign n) →
             ∀ y → outBit (toPS {k = k} st) x y w ≡ not (x w))
settled {k = k} st free = by (some-or-all (λ w → verdict (sig st w) w (free w)))
  where
  by : (∃ λ w → ∃ λ x → ∀ y → valᴸ (sig st w) x y ≡ not (x w)) ⊎
       (∀ w x y → valᴸ (sig st w) x y ≡ x w) → _
  by (inj₁ (w , x , miss)) = inj₂ (w , x , λ y →
    trans (outBit-liftᴸ (toPS {k = k} st) x y w (sig st w) refl) (miss y))
  by (inj₂ solved) = inj₁ (λ w x y →
    trans (outBit-liftᴸ (toPS {k = k} st) x y w (sig st w) refl)
          (solved w x y))

-- Gauss's verdict, through the general restriction: refuted, or, for a
-- well-formed path-sum, decided by the end of the elimination.

linear-verdict : (st : State n m) → WellFormed (toPS {k = k} st) →
                 ¬ (toPS {k = k} st ≋ idPS) ⊎
                 (∃ λ m′ → ∃ λ (st′ : State n m′) →
                    (toPS {k = k} st ↝* toPS {k = k} st′) ×
                    (∀ w → Solved (toPS {k = k} st′) w) ×
                    (toPS {k = k} st ≋ idPS ⇔ toPS {k = k} st′ ≋ idPS))
linear-verdict {k = k} st wf = by (settled {k = k} final free)
  where
  open Eliminated (eliminate {k = k} st)

  by : (∀ w → Solved (toPS {k = k} final) w) ⊎
       (∃ λ w → ∃ λ x → ∀ y → outBit (toPS {k = k} final) x y w ≡ not (x w)) →
       _
  by (inj₁ solved)          = inj₂ (left , final , chain , solved ,
    restriction-solved (toPS st) (toPS final) wf (↝*⇒⇝* chain) solved)
  by (inj₂ (w , x , miss)) =
    inj₁ (restriction-refutes (toPS st) (toPS final) (↝*⇒⇝* chain) w x miss)
