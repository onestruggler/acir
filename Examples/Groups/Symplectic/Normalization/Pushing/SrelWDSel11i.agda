------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on (₁₊a1',b1)/(₁₊a2',b2), sub-case βα.
--
-- The c11 mirror of SrelWDSel10m (c10-go-aaβα).  Under the mirror the
-- roles of the two boxes exchange: c10 splits on b₂ + -a₁ and b₂ + a₂,
-- c11 on b₁ + -a₂ and b₁ + a₁, and c11's H ↓ / S⁻¹ ↓ act on the FIRST
-- box where c10's H ↑ / S⁻¹ ↑ act on the second.
--
-- Built bottom-up.  This file currently establishes the value kit and
-- the coset (≡) half; the residual (≈) half needs its own word identity
-- and is not yet here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11i
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

------------------------------------------------------------------------
-- The value kit, mirrored from SrelWDSel10m's.
--
-- Hypotheses:  eqY : b1 + - ₁₊ a2' ≡ ₁₊ w   (branch β on the first split)
--              eqZ : b1 + ₁₊ a1'  ≡ ₀       (branch α on the second)

module Values (a1' a2' w : Fin (₁₊ p-2)) (b1 : ℤ ₚ)
  (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) (eqZ : b1 + ₁₊ a1' ≡ ₀) where

  -- eqZ pins b1 to -a₁.
  b1nA1 : b1 ≡ - ₁₊ a1'
  b1nA1 = Eq.trans (Eq.sym (+-identityʳ b1))
    (Eq.trans (Eq.cong (b1 +_) (Eq.sym (+-inverseʳ (₁₊ a1'))))
    (Eq.trans (Eq.sym (+-assoc b1 (₁₊ a1') (- ₁₊ a1')))
    (Eq.trans (Eq.cong (_+ - ₁₊ a1') eqZ)
      (+-identityˡ (- ₁₊ a1')))))

  -- hence w ≡ -(a₁ + a₂), the mirror of SrelWDSel10m's ySum.
  wSum : ₁₊ w ≡ - (₁₊ a1' + ₁₊ a2')
  wSum = Eq.trans (Eq.sym eqY)
    (Eq.trans (Eq.cong (_+ - ₁₊ a2') b1nA1)
      (-‿+-comm (₁₊ a1') (₁₊ a2')))

  negw : - ₁₊ w ≡ ₁₊ a1' + ₁₊ a2'
  negw = Eq.trans (Eq.cong -_ wSum) (-‿involutive (₁₊ a1' + ₁₊ a2'))

  -- the first box's b-component after the second CZ
  vfix : - ₁₊ a1' + - ₁₊ a2' ≡ ₁₊ w
  vfix = Eq.sym (Eq.trans wSum (Eq.sym (-‿+-comm (₁₊ a1') (₁₊ a2'))))

  nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
  nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

  nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
  nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

  nfixw : nsum p-1 (- ₁₊ w) ≡ ₁₊ w
  nfixw = Eq.trans (nsum-p-1 (- ₁₊ w)) (-‿involutive (₁₊ w))

  e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
  e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

  -- The first box's S⁻¹ escape closes: b1 + nsum p-1 (-a₁) ≡ ₀.
  r1fix : b1 + nsum p-1 (- ₁₊ a1') ≡ ₀
  r1fix = Eq.trans (Eq.cong (b1 +_) nfixa1) eqZ

  -- The re-turned first box after the second S⁻¹.
  r6fix : - ₀ + nsum p-1 (- ₁₊ w) ≡ ₁₊ w
  r6fix = Eq.trans (Eq.cong₂ _+_ -0#≈0# nfixw) (+-identityˡ (₁₊ w))

  -- The two sides' second box agree: both are b2 + a₂.
  d2fix : ∀ (b2 : ℤ ₚ) → (b2 + - ₁₊ a1') + - ₁₊ w ≡ (b2 + - ₀) + ₁₊ a2'
  d2fix b2 = Eq.trans (Eq.cong ((b2 + - ₁₊ a1') +_) negw)
    (Eq.trans (+-assoc b2 (- ₁₊ a1') (₁₊ a1' + ₁₊ a2'))
    (Eq.trans (Eq.cong (b2 +_)
        (Eq.sym (+-assoc (- ₁₊ a1') (₁₊ a1') (₁₊ a2'))))
    (Eq.trans (Eq.cong (λ t → b2 + (t + ₁₊ a2')) (+-inverseˡ (₁₊ a1')))
    (Eq.trans (Eq.cong (b2 +_) (+-identityˡ (₁₊ a2')))
      (Eq.cong (_+ ₁₊ a2') (Eq.sym (e0 b2)))))))

------------------------------------------------------------------------
-- The coset half.
--
-- LHS word CZ • H ↓ • CZ threaded from inj₂ ((A1,b1) , inj₂ ((A2,b2) , lm2)):
--   CZ  : (A1, b1 - A2) (A2, b2 - A1)
--   H ↓ : Hd' (A1, b1 - A2) = Hd' (A1, ₁₊ w) = (₁₊ w, -A1)   [by eqY]
--   CZ  : (₁₊ w, -A1 - A2) (A2, (b2 - A1) - ₁₊ w)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  c11-βα-L-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    b1 + - ₁₊ a2' ≡ ₁₊ w → b1 + ₁₊ a1' ≡ ₀ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) .proj₂
    ≡ inj₂ ((₁₊ w , ₁₊ w) ,
        inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₁₊ w) , lm2))
  c11-βα-L-coset b1 b2 a1' a2' w lm2 eqY eqZ =
    Eq.trans
      (Eq.cong (λ v → ((ract2 ᵗ)
          (inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2))) CZ) .proj₂)
        eqY)
      (Eq.cong (λ v → inj₂ ((₁₊ w , v) ,
          inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₁₊ w) , lm2)))
        (Values.vfix a1' a2' w b1 eqY eqZ))

------------------------------------------------------------------------
-- The RHS coset trace.
--
--   S⁻¹ ↓ : (A1, b1)  ↦ (A1, ₀)              [r1fix]
--   H ↓   : (A1, ₀)   ↦ (₀, -A1)
--   S⁻¹ ↓ : (₀, -A1)  fixed                  [it-dDS-a0]
--   CZ    : (₀, -A1 - A2) (A2, b2 - ₀)       and -A1 - A2 ≡ ₁₊ w  [vfix]
--   H ↓   : (₀, ₁₊ w) ↦ (₁₊ w, - ₀)
--   S⁻¹ ↓ : (₁₊ w, -₀) ↦ (₁₊ w, ₁₊ w)        [r6fix]
--   S⁻¹ ↑ : second box ↦ (A2, (b2 - ₀) + A2)

  private
    REST : Word (Gen (₃₊ m))
    REST = H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

  -- RHS step 1 of 7: the bottom S⁻¹ closes the first box's b-component.
  c11-βα-R-step1 : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓)) .proj₂
    ≡ inj₂ ((₁₊ a1' , ₀) , inj₂ ((₁₊ a2' , b2) , lm2))
  c11-βα-R-step1 b1 b2 a1' a2' w lm2 eqY eqZ = Eq.trans
    (Eq.cong (λ u → ((ract2 ᵗ)
        (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2))) u) .proj₂)
      (↓-pow-S p-1))
    (Eq.trans (ract-S^-coset (₁₊ a1' , b1) (inj₂ ((₁₊ a2' , b2) , lm2)) p-1)
      (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2) , lm2)))
        (Eq.trans (it-dDS-nz p-1 (₁₊ a1') b1 (λ ()))
          (Eq.cong (₁₊ a1' ,_) (Values.r1fix a1' a2' w b1 eqY eqZ)))))

------------------------------------------------------------------------
-- The full RHS coset trace.
--
-- Steps 2, 4 and 5 are definitional: Hd' reduces on a box whose
-- components are already in constructor form, and the CZ clause never
-- inspects the D components.  Only the three S⁻¹ steps and the two
-- value rewrites need work.

  c11-βα-R-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    ≡ inj₂ ((₁₊ w , ₁₊ w) ,
        inj₂ ((₁₊ a2' , (b2 + - ₀) + ₁₊ a2') , lm2))
  c11-βα-R-coset b1 b2 a1' a2' w lm2 eqY eqZ =
    Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c REST1) .proj₂)
                (c11-βα-R-step1 b1 b2 a1' a2' w lm2 eqY eqZ))
    (Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c REST3) .proj₂) s3)
    (Eq.trans (Eq.cong (λ v → ((ract2 ᵗ)
                  (inj₂ ((₀ , v) ,
                    inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) REST4) .proj₂)
                (Values.vfix a1' a2' w b1 eqY eqZ))
              s7))
    where
    open Values a1' a2' w b1 eqY eqZ

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    REST1 : Word (Gen (₃₊ m))
    REST1 = H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    REST3 : Word (Gen (₃₊ m))
    REST3 = CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    REST4 : Word (Gen (₃₊ m))
    REST4 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    -- step 3: S⁻¹ fixes an a = ₀ box.
    s3 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) (S⁻¹ ↓)) .proj₂
         ≡ inj₂ ((₀ , - ₁₊ a1') , lm)
    s3 = Eq.trans
      (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) u) .proj₂)
        (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₀ , - ₁₊ a1') lm p-1)
        (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (- ₁₊ a1'))))

    -- steps 6 and 7 together, from the coset reached after step 5.
    s7 : ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
            inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
         ≡ inj₂ ((₁₊ w , ₁₊ w) ,
             inj₂ ((₁₊ a2' , (b2 + - ₀) + ₁₊ a2') , lm2))
    s7 = Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c (S⁻¹ ↑)) .proj₂) s6) s7'
      where
      s6 : ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↓)) .proj₂
           ≡ inj₂ ((₁₊ w , ₁₊ w) ,
               inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))
      s6 = Eq.trans
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
            inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
        (Eq.trans (ract-S^-coset (₁₊ w , - ₀)
            (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
            (Eq.trans (it-dDS-nz p-1 (₁₊ w) (- ₀) (λ ()))
              (Eq.cong (₁₊ w ,_) r6fix))))

      s7' : ((ract2 ᵗ) (inj₂ ((₁₊ w , ₁₊ w) ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↑)) .proj₂
            ≡ inj₂ ((₁₊ w , ₁₊ w) ,
                inj₂ ((₁₊ a2' , (b2 + - ₀) + ₁₊ a2') , lm2))
      s7' = Eq.trans
        (Eq.cong proj₂ (ract-↑-≡ (₁₊ w , ₁₊ w)
          (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) S⁻¹))
        (Eq.cong (λ c → inj₂ ((₁₊ w , ₁₊ w) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₀) (λ ()))
                (Eq.cong (₁₊ a2' ,_)
                  (Eq.cong ((b2 + - ₀) +_) nfixa2))))))

------------------------------------------------------------------------
-- The coset half of c11-go-aaβα, complete.

  c11-βα-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) .proj₂
    ≡ ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
  c11-βα-coset b1 b2 a1' a2' w lm2 eqY eqZ =
    Eq.trans (c11-βα-L-coset b1 b2 a1' a2' w lm2 eqY eqZ)
    (Eq.trans (Eq.cong (λ v → inj₂ ((₁₊ w , ₁₊ w) ,
                  inj₂ ((₁₊ a2' , v) , lm2)))
                (Values.d2fix a1' a2' w b1 eqY eqZ b2))
      (Eq.sym (c11-βα-R-coset b1 b2 a1' a2' w lm2 eqY eqZ)))

------------------------------------------------------------------------
-- The residual side: the LHS escape, as an explicit word.
--
-- Both CZs meet two a≠0 boxes, so both emit the clause-4 pad (padSA);
-- between them the bottom H meets the a≠0 box (A1, ₁₊ w) and emits the
-- clause-4 unit (hpad).  Note the depth: c11's H ↓ emits at ↓ᵏ (₁₊ m),
-- where c10's H ↑ emitted (… ↓ᵏ m) ↑.

  c11-βα-L-resid : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) .proj₁
    ≡ ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
          inj₂ ((₁₊ a2' , b2) , lm2))) CZ) .proj₁
      • ((Hdir (₁₊ a1' , ₁₊ w) ↓ᵏ (₁₊ m))
         • ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₁₊ a1') ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2))) CZ) .proj₁)
  c11-βα-L-resid b1 b2 a1' a2' w lm2 eqY eqZ =
    Eq.cong₂ _•_ Eq.refl
      (Eq.cong₂ _•_
        (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) eqY)
        (Eq.cong (λ c → ((ract2 ᵗ) c CZ) .proj₁)
          (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
            eqY)))

------------------------------------------------------------------------
-- The RHS escapes, one step at a time (pair-valued, so the coset
-- threads through).
--
--   1. S⁻¹ ↓ on an a≠0 box  — escape ≈ ε          (ract-S^-resid-a+)
--   2. H ↓  on (A1, ₀)      — escape Hdir (A1,₀) ↓ᵏ (₁₊ m), definitional
--   3. S⁻¹ ↓ on an a=₀ box  — escape ≡ S ^ p-1    (ract-S^-resid-a0)
--   4. CZ on (₀,·),(A2,·)   — the a=₀/a≠0 dir-of branch
--   5. H ↓ on (₀, ₁₊ w)     — escape Hdir (₀,₁₊w) ↓ᵏ (₁₊ m), definitional
--   6. S⁻¹ ↓ on an a≠0 box  — escape ≈ ε
--   7. S⁻¹ ↑ on an a≠0 box  — escape ≈ ε, under ↑

  module RSteps (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m))
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) (eqZ : b1 + ₁₊ a1' ≡ ₀) where

    open Values a1' a2' w b1 eqY eqZ public

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    E₁raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) S⁻¹) .proj₁

    -- step 1
    r1 : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↓))
         ≡ (E₁raw , inj₂ ((₁₊ a1' , ₀) , lm))
    r1 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) u)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , b1) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') b1 (λ ()))
              (Eq.cong (₁₊ a1' ,_) r1fix)))))

    -- step 3
    r3 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) (S⁻¹ ↓))
         ≡ (S ^ p-1 , inj₂ ((₀ , - ₁₊ a1') , lm))
    r3 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) u)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ a1') lm p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (- ₁₊ a1')))))

    -- step 6
    r6 : ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↓))
         ≡ (E₆raw , inj₂ ((₁₊ w , ₁₊ w) ,
             inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₁₊ w , - ₀) ,
          inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) u)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ w , - ₀)
            (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)))
            (Eq.trans (it-dDS-nz p-1 (₁₊ w) (- ₀) (λ ()))
              (Eq.cong (₁₊ w ,_) r6fix)))))

    -- the three escapes that vanish
    E₁≈ε : E₁raw ≈ ε
    E₁≈ε = ract-S^-resid-a+ (₁₊ a1' , b1) lm p-1 (λ ())

    E₆≈ε : E₆raw ≈ ε
    E₆≈ε = ract-S^-resid-a+ (₁₊ w , - ₀)
             (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) p-1 (λ ())

    E₇≈ε : E₇raw ↑ ≈ ε
    E₇≈ε = trans (lemma-cong↑ E₇raw ε
             (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₀) lm2 p-1 (λ ()))) refl

    -- The two H escapes and the second CZ pad, named.
    HH2 CZpad Hw : Word (Gen (₂₊ m))
    HH2   = Hdir (₁₊ a1' , ₀) ↓ᵏ (₁₊ m)
    CZpad = ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) CZ) .proj₁
    Hw    = Hdir (₀ , ₁₊ w) ↓ᵏ (₁₊ m)

    REST1 REST3 REST4 : Word (Gen (₃₊ m))
    REST1 = H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
    REST3 = CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
    REST4 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    -- step 7's escape, unwrapped.
    r7 : ((ract2 ᵗ) (inj₂ ((₁₊ w , ₁₊ w) ,
           inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) (S⁻¹ ↑)) .proj₁
         ≡ E₇raw ↑
    r7 = Eq.cong proj₁ (ract-↑-≡ (₁₊ w , ₁₊ w)
           (inj₂ ((₁₊ a2' , b2 + - ₀) , lm2)) S⁻¹)

    -- The whole RHS escape, as an explicit seven-factor word.
    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
            ≡ E₁raw • (HH2 • ((S ^ p-1) •
                (CZpad • (Hw • (E₆raw • (E₇raw ↑))))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) REST1) .proj₁) r1)
      (Eq.cong (E₁raw •_)
      (Eq.cong (HH2 •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) REST3) .proj₁) r3)
      (Eq.cong ((S ^ p-1) •_)
      (Eq.cong (CZpad •_)
      (Eq.trans (Eq.cong
          (λ v → ((ract2 ᵗ) (inj₂ ((₀ , v) ,
              inj₂ ((₁₊ a2' , b2 + - ₀) , lm2))) REST4) .proj₁)
          vfix)
      (Eq.cong (Hw •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁) r6)
        (Eq.cong (E₆raw •_) r7)))))))))

    -- Everything except the two H escapes and the S-power cancels.
    Rclean : E₁raw • (HH2 • ((S ^ p-1) •
               (CZpad • (Hw • (E₆raw • (E₇raw ↑))))))
             ≈ HH2 • ((S ^ p-1) • CZpad)
    Rclean = trans (cleft E₁≈ε) (trans left-unit
      (cright (cright (trans (cright Zε) right-unit))))
      where
      -- Hw is Hdir (₀ , ₁₊ w) ↓ᵏ _, and Hdir on an a=₀,b≠₀ box is ε,
      -- so the tail collapses entirely.
      Zε : Hw • (E₆raw • (E₇raw ↑)) ≈ ε
      Zε = trans left-unit (trans (cleft E₆≈ε) (trans left-unit E₇≈ε))

    ------------------------------------------------------------------
    -- The LHS escape, with both CZ pads expanded.

    PADg PADy HU : Word (Gen (₂₊ m))
    PADg = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑
        • (H ↑) ^ 3)))))
    PADy = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ w , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ w * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑
        • (H ↑) ^ 3)))))
    HU   = Hdir (₁₊ a1' , ₁₊ w) ↓ᵏ (₁₊ m)

    L-pads : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
               .proj₁ ≡ PADg • (HU • PADy)
    L-pads = Eq.cong₂ _•_ (padSA a1' a2' b1 b2)
      (Eq.cong₂ _•_
        (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) eqY)
        (Eq.trans
          (Eq.cong (λ c → ((ract2 ᵗ) c CZ) .proj₁)
            (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
                inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
              eqY))
          (padSA w a2' (- ₁₊ a1') (b2 + - ₁₊ a1'))))

    ------------------------------------------------------------------
    -- WHAT REMAINS for this sub-case: the word identity.
    --
    -- Recorded as a well-typed Set, NOT postulated and NOT inhabited —
    -- exactly the shape of RhoExDirect.ρ-Ex-Goal.  Everything else in
    -- the βα branch is proved; `c11-go-aaβα` below takes it as an
    -- argument, so supplying an inhabitant finishes SrelWD.agda:374.
    --
    -- It is the c11 analogue of SrelWDSel10l.idβα (409 lines there).

    idβα-c11-Goal : Set
    idβα-c11-Goal = PADg • (HU • PADy) ≈ HH2 • ((S ^ p-1) • CZpad)

------------------------------------------------------------------------
-- The βα sub-case, complete modulo the word identity.

  c11-go-aaβα : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    RSteps.idβα-c11-Goal b1 b2 a1' a2' w lm2 eqY eqZ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-aaβα b1 b2 a1' a2' w lm2 eqY eqZ ident =
    resid≈ , c11-βα-coset b1 b2 a1' a2' w lm2 eqY eqZ
    where
    open RSteps b1 b2 a1' a2' w lm2 eqY eqZ

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ = trans (refl' L-pads)
      (trans ident (sym (trans (refl' R-fix) Rclean)))
