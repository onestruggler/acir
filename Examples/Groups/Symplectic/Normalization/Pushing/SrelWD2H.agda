------------------------------------------------------------------------
-- Presentations of groups
--
-- Width-2 well-definedness pairs for the kHn-heavy unary families
-- (order-H, order-SH, comm-HHS) at inj₁ cosets: the per-branch coset
-- halves of PushWD paired with StrategyB2.wd-from-coset, dispatched
-- over the A box with the same elim-suc/elim-fin hypothesis shapes as
-- the width-1 clauses.  Kept in its own leaf: these families'
-- conversions are checker-heavy.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWD2H
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (inj₁)
open import Data.Vec using (Vec)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C ; ract ; _≋_ ; elim-suc ; elim-fin ; neg≢0)
import Examples.Groups.Symplectic.Normalization.Pushing.PushWD
  p-2 p-prime as PW
import Examples.Groups.Symplectic.Normalization.Pushing.StrategyB2
  p-2 p-prime as SB2

------------------------------------------------------------------------
-- order-H: the fully-nonzero branch (the SrelWD hole; the other
-- branches are filled in SrelWD itself).

order-H-wd2-inj₁-nn : ∀ (mm : M 2) (bv : Vec B 1) (a₀ b₀ : Fin (₁₊ p-2))
  (nz : (₁₊ a₀ , ₁₊ b₀) ≢ (₀ , ₀)) →
  let c = inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))) in
  (ract {1} ᵗ) c (H ^ 4) ≋ (ract {1} ᵗ) c ε
order-H-wd2-inj₁-nn mm bv a₀ b₀ nz =
  elim-suc (- ₁₊ a₀) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- ₁₊ b₀) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-suc (- ₁₊ y) (neg≢0 (₁₊ y) λ ()) λ w eq-w →
  SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
    (srel Base.order-H)
    (PW.OrderH-nn.orderH-inj₁-nn-coset
      mm bv a₀ b₀ nz y eq-y z eq-z w eq-w)

------------------------------------------------------------------------
-- order-SH: all four branches, dispatched over the A box.

order-SH-wd2-inj₁ : ∀ (mm : M 2) (bv : Vec B 1) (ab : ℤ ₚ × ℤ ₚ)
  (nz : ab ≢ (₀ , ₀)) →
  let c = inj₁ (mm , (bv , (ab , nz))) in
  (ract {1} ᵗ) c ((S • H) ^ 3) ≋ (ract {1} ᵗ) c ε
order-SH-wd2-inj₁ mm bv (₀ , ₀) nz = ⊥-elim (nz auto)
order-SH-wd2-inj₁ mm bv (₀ , ₁₊ b₀) nz =
  elim-suc (- ₁₊ b₀) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  SB2.wd-from-coset (inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz))))
    (srel Base.order-SH)
    (PW.OrderSH-0b.orderSH-inj₁-0b-coset mm bv b₀ nz z eq-z)
order-SH-wd2-inj₁ mm bv (₁₊ a₀ , ₀) nz =
  elim-suc (- ₁₊ a₀) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , nz))))
    (srel Base.order-SH)
    (PW.OrderSH-a0.orderSH-inj₁-a0-coset mm bv a₀ nz y eq-y)
order-SH-wd2-inj₁ mm bv (₁₊ a₀ , ₁₊ b₀) nz =
  elim-suc (- ₁₊ a₀) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- ₁₊ b₀) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - ₁₊ a₀)
    (λ Xeq →
      SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (srel Base.order-SH)
        (PW.OrderSH-nn0.orderSH-inj₁-nn0-coset mm bv a₀ b₀ nz y eq-y Xeq))
    (λ w Xeq →
      elim-suc (- ₁₊ w) (neg≢0 (₁₊ w) λ ()) λ t eq-t →
      SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (srel Base.order-SH)
        (PW.OrderSH-nnw.orderSH-inj₁-nnw-coset
          mm bv a₀ b₀ nz y eq-y z eq-z w Xeq t eq-t))

------------------------------------------------------------------------
-- comm-HHS: all four branches, dispatched over the A box.

comm-HHS-wd2-inj₁ : ∀ (mm : M 2) (bv : Vec B 1) (ab : ℤ ₚ × ℤ ₚ)
  (nz : ab ≢ (₀ , ₀)) →
  let c = inj₁ (mm , (bv , (ab , nz))) in
  (ract {1} ᵗ) c (H • H • S) ≋ (ract {1} ᵗ) c (S • H • H)
comm-HHS-wd2-inj₁ mm bv (₀ , ₀) nz = ⊥-elim (nz auto)
comm-HHS-wd2-inj₁ mm bv (₀ , ₁₊ b₀) nz =
  elim-suc (- ₁₊ b₀) (neg≢0 (₁₊ b₀) λ ()) λ y eq-y →
  SB2.wd-from-coset (inj₁ (mm , (bv , ((₀ , ₁₊ b₀) , nz))))
    (srel Base.comm-HHS)
    (PW.CommHHS-0b.commHHS-inj₁-0b-coset mm bv b₀ nz y eq-y)
comm-HHS-wd2-inj₁ mm bv (₁₊ a₀ , ₀) nz =
  elim-suc (- ₁₊ a₀) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₀) , nz))))
    (srel Base.comm-HHS)
    (PW.CommHHS-a0.commHHS-inj₁-a0-coset mm bv a₀ nz y eq-y)
comm-HHS-wd2-inj₁ mm bv (₁₊ a₀ , ₁₊ b₀) nz =
  elim-suc (- ₁₊ a₀) (neg≢0 (₁₊ a₀) λ ()) λ y eq-y →
  elim-suc (- ₁₊ b₀) (neg≢0 (₁₊ b₀) λ ()) λ z eq-z →
  elim-fin (₁₊ b₀ + - ₁₊ a₀)
    (λ Xeq →
      SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (srel Base.comm-HHS)
        (PW.CommHHS-nn0.commHHS-inj₁-nn0-coset
          mm bv a₀ b₀ nz y z eq-y eq-z Xeq))
    (λ w Xeq →
      SB2.wd-from-coset (inj₁ (mm , (bv , ((₁₊ a₀ , ₁₊ b₀) , nz))))
        (srel Base.comm-HHS)
        (PW.CommHHS-nnw.commHHS-inj₁-nnw-coset
          mm bv a₀ b₀ nz y z w eq-y eq-z Xeq))
