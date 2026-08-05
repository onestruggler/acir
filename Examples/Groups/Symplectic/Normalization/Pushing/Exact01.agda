------------------------------------------------------------------------
-- Presentations of groups
--
-- Exactness of the width-1 coset table on sections: running the table
-- from the identity coset over a coset's section word returns that
-- coset (sect-coset).  With it, Tower01's Transfer.Unique yields the
-- exact width-1 normal form: nf' ∘ gg ≡ id on ⊤ × C 1.
--
-- The section at width 1 is S^(−e) • (ε • [ a ]ᵃ); the table runs are
-- computed by ract1-S^-a0 (the S-power orbit at the identity box, whose
-- emission constant is 1²), ractM! (the M-word leg), the definitional
-- H step at a (₀,b) box (emission 0, box ↦ (b,0)), and ract1-S^-a+
-- (the closing S-power at an a≠0 box).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Exact01
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)

open import Word.Base

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
  using (C ; ract ; mk ; c1-eq ; e+-0 ; kS-a0 ; ract1-S^-a0 ; ract1-S^-a+ ; nsum)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDM
  p-2 p-prime using (ractM! ; nsum-neg ; Mact-nz)
import Examples.Groups.Symplectic.Normalization.Pushing.Tower01
  p-2 p-prime as T01
open T01 using (Ia ; I₀)

------------------------------------------------------------------------
-- The S^(−e) leg: from the identity coset, the S-power orbit at the
-- (₀,₁) box accumulates exactly e in the E slot (the emission constant
-- kS-a0 at the identity box is 1⁻¹·1⁻¹ ≡ 1).

nzI : (₀ , ₁) ≢ (₀ , ₀)
nzI = Ia .proj₂

K1≡₁ : kS-a0 ₀ nzI ≡ ₁
K1≡₁ = Eq.trans (Eq.cong₂ _*_ inv-₁ inv-₁) (*-identityˡ ₁)

c₁ : ∀ (e : E) → ((ract {0} ᵗ) I₀ (S^ (- e))) .proj₂ ≡ mk e (₀ , ₁) nzI
c₁ e = Eq.trans (ract1-S^-a0 (toℕ (- e)) ₀ ₀ nzI)
               (c1-eq e-alg Eq.refl)
  where
  e-alg : ₀ + nsum (toℕ (- e)) (- kS-a0 ₀ nzI) ≡ e
  e-alg = Eq.trans (+-identityˡ _)
          (Eq.trans (nsum-neg (- e) (kS-a0 ₀ nzI))
          (Eq.trans (Eq.cong (λ z → - (- e * z)) K1≡₁)
          (Eq.trans (Eq.cong -_ (*-identityʳ (- e)))
                    (-‿involutive e))))

------------------------------------------------------------------------
-- Exactness of the table on sections.

sect-coset : ∀ (c : C 1) → ((ract {0} ᵗ) I₀ [ c ]ᵐˡ) .proj₂ ≡ c
sect-coset (([] , e) , ([] , ((₀ , ₀) , nz))) = ⊥-elim (nz auto)
-- a = 0: the section is S^(−e) • (ε • (ZM (b⁻¹) • ε)); the M leg maps
-- the identity box (₀,₁) to (₀ , b⁻¹⁻¹·1) = (₀ , b).
sect-coset (([] , e) , ([] , ((₀ , ₁₊ b') , nz))) =
  Eq.trans (Eq.cong (λ z → ((ract {0} ᵗ) z (ZM x*)) .proj₂) (c₁ e))
  (Eq.trans (ractM! x* e (₀ , ₁) nzI (Mact-nz x* (₀ , ₁) nzI))
            (c1-eq Eq.refl box-alg))
  where
  x* : ℤ* ₚ
  x* = (₁₊ b' , λ ()) ⁻¹

  box-alg : (x* .proj₁ * ₀ , (x* ⁻¹) .proj₁ * ₁) ≡ (₀ , ₁₊ b')
  box-alg = Eq.cong₂ _,_ (*-zeroʳ (x* .proj₁))
            (Eq.trans (*-identityʳ ((x* ⁻¹) .proj₁))
                      (inv-involutive (₁₊ b' , λ ())))
-- a ≠ 0: the section is S^(−e) • (ε • (ZM (a⁻¹) • (H • S^(−b·a⁻¹))));
-- the M leg maps (₀,₁) to (₀,a), the H step (emission 0) to (a,₀), and
-- the closing S-power writes b into the second slot (each step adds −a,
-- and −((−b·a⁻¹)·a) = b).
sect-coset (([] , e) , ([] , ((₁₊ a' , b) , nz))) =
  Eq.trans (Eq.cong (λ z → ((ract {0} ᵗ) z (ZM y* • (H • S^ mba))) .proj₂)
            (c₁ e))
  (Eq.trans (Eq.cong (λ z → ((ract {0} ᵗ) z (H • S^ mba)) .proj₂)
             (Eq.trans (ractM! y* e (₀ , ₁) nzI (Mact-nz y* (₀ , ₁) nzI))
                       (c1-eq {nz' = nzA} Eq.refl mbox)))
  (Eq.trans (Eq.cong (λ z → ((ract {0} ᵗ) z (S^ mba)) .proj₂) hfix)
  (Eq.trans (ract1-S^-a+ (toℕ mba) e a' ₀ nzA0)
            (c1-eq Eq.refl final-box))))
  where
  y* : ℤ* ₚ
  y* = (₁₊ a' , λ ()) ⁻¹

  a⁻¹ = y* .proj₁
  mba = - b * a⁻¹

  nzA : (₀ , ₁₊ a') ≢ (₀ , ₀)
  nzA = λ ()

  nzA0 : (₁₊ a' , ₀) ≢ (₀ , ₀)
  nzA0 = λ ()

  mbox : (y* .proj₁ * ₀ , (y* ⁻¹) .proj₁ * ₁) ≡ (₀ , ₁₊ a')
  mbox = Eq.cong₂ _,_ (*-zeroʳ (y* .proj₁))
         (Eq.trans (*-identityʳ ((y* ⁻¹) .proj₁))
                   (inv-involutive (₁₊ a' , λ ())))

  -- The H step at the (₀,a) box: emission constant 0, box ↦ (a,₀).
  hfix : ((ract {0} ᵗ) (mk e (₀ , ₁₊ a') nzA) H) .proj₂ ≡ mk e (₁₊ a' , ₀) nzA0
  hfix = c1-eq (e+-0 e) Eq.refl

  invl : a⁻¹ * ₁₊ a' ≡ ₁
  invl = lemma-⁻¹ˡ (₁₊ a') {{nztoℕ {y = ₁₊ a'} {neq0 = λ ()}}}

  snd-alg : ₀ + nsum (toℕ mba) (- (₁₊ a')) ≡ b
  snd-alg = Eq.trans (+-identityˡ _)
            (Eq.trans (nsum-neg mba (₁₊ a'))
            (Eq.trans (Eq.cong -_
              (Eq.trans (*-assoc (- b) a⁻¹ (₁₊ a'))
              (Eq.trans (Eq.cong ((- b) *_) invl) (*-identityʳ (- b)))))
            (-‿involutive b)))

  final-box : (₁₊ a' , ₀ + nsum (toℕ mba) (- (₁₊ a'))) ≡ (₁₊ a' , b)
  final-box = Eq.cong (₁₊ a' ,_) snd-alg

------------------------------------------------------------------------
-- The exact width-1 normal form: Transfer.Unique with the trivial base
-- (exact on ⊤ by η) and the grouplike witness for the width-1
-- presentation.

open Symplectic-GroupLike using (grouplike)

module UQ = T01.TR01.Unique grouplike sect-coset T01.nf₀ (λ u → Eq.refl)

-- nf'∘gg=id : the transported width-1 normal form is exact.
open UQ public using (nf'∘gg=id)
