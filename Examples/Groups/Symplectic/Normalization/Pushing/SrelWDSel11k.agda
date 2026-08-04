------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on (₁₊a1',b1)/(₁₊a2',b2), sub-case ββ.
--
-- Y = b₁ - a₂ ≡ w and Z = b₁ + a₁ ≡ z, both nonzero, so b₁ ≡ w + a₂ and
-- z ≡ (w + a₂) + a₁.  Every box the two sides meet has a ≠ ₀, so all
-- four H escapes are clause-4 units and both CZs on each side are the
-- padSA pad; nothing degenerates.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11k
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
  using (-0#≈0# ; -‿involutive ; -‿+-comm
       ; -‿distribˡ-* ; -‿distribʳ-*)

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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

------------------------------------------------------------------------
-- The value kit.
--
--   eqY : b1 + - ₁₊ a2' ≡ ₁₊ w   ⇒  b1 ≡ w + a₂
--   eqZ : b1 + ₁₊ a1'  ≡ ₁₊ z    ⇒  z  ≡ (w + a₂) + a₁

module Values (a1' a2' w z : Fin (₁₊ p-2)) (b1 : ℤ ₚ)
  (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) where

  b1val : b1 ≡ ₁₊ w + ₁₊ a2'
  b1val = Eq.trans (Eq.sym (+-identityʳ b1))
    (Eq.trans (Eq.cong (b1 +_) (Eq.sym (+-inverseˡ (₁₊ a2'))))
    (Eq.trans (Eq.sym (+-assoc b1 (- ₁₊ a2') (₁₊ a2')))
      (Eq.cong (_+ ₁₊ a2') eqY)))

  zSum : ₁₊ z ≡ (₁₊ w + ₁₊ a2') + ₁₊ a1'
  zSum = Eq.trans (Eq.sym eqZ) (Eq.cong (_+ ₁₊ a1') b1val)

  nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
  nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

  nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
  nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

  nfixw : nsum p-1 (- ₁₊ w) ≡ ₁₊ w
  nfixw = Eq.trans (nsum-p-1 (- ₁₊ w)) (-‿involutive (₁₊ w))

  nfixz : nsum p-1 (- ₁₊ z) ≡ ₁₊ z
  nfixz = Eq.trans (nsum-p-1 (- ₁₊ z)) (-‿involutive (₁₊ z))

  -- - z ≡ (-w + -a₂) + -a₁
  negz : - ₁₊ z ≡ (- ₁₊ w + - ₁₊ a2') + - ₁₊ a1'
  negz = Eq.trans (Eq.cong -_ zSum)
    (Eq.trans (Eq.sym (-‿+-comm (₁₊ w + ₁₊ a2') (₁₊ a1')))
      (Eq.cong (_+ - ₁₊ a1') (Eq.sym (-‿+-comm (₁₊ w) (₁₊ a2')))))

  -- first box after the second CZ, on both sides
  vfix : - ₁₊ a1' + - ₁₊ a2' ≡ - ₁₊ z + ₁₊ w
  vfix = Eq.sym
    (Eq.trans (Eq.cong (_+ ₁₊ w) negz)
    (Eq.trans (+-assoc (- ₁₊ w + - ₁₊ a2') (- ₁₊ a1') (₁₊ w))
    (Eq.trans (Eq.cong ((- ₁₊ w + - ₁₊ a2') +_) (+-comm (- ₁₊ a1') (₁₊ w)))
    (Eq.trans (Eq.sym (+-assoc (- ₁₊ w + - ₁₊ a2') (₁₊ w) (- ₁₊ a1')))
    (Eq.trans (Eq.cong (_+ - ₁₊ a1')
      (Eq.trans (+-assoc (- ₁₊ w) (- ₁₊ a2') (₁₊ w))
      (Eq.trans (Eq.cong (- ₁₊ w +_) (+-comm (- ₁₊ a2') (₁₊ w)))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ w) (₁₊ w) (- ₁₊ a2')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a2') (+-inverseˡ (₁₊ w)))
        (+-identityˡ (- ₁₊ a2')))))))
      (+-comm (- ₁₊ a2') (- ₁₊ a1')))))))

  e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
  e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

  r1fix : b1 + nsum p-1 (- ₁₊ a1') ≡ ₁₊ z
  r1fix = Eq.trans (Eq.cong (b1 +_) nfixa1) eqZ

  r3fix : - ₁₊ a1' + nsum p-1 (- ₁₊ z) ≡ - ₁₊ a1' + ₁₊ z
  r3fix = Eq.cong (- ₁₊ a1' +_) nfixz

  -- after the R-side CZ the bottom box's b is w again
  r5fix : (- ₁₊ a1' + ₁₊ z) + - ₁₊ a2' ≡ ₁₊ w
  r5fix = Eq.trans (Eq.cong (λ t → (- ₁₊ a1' + t) + - ₁₊ a2') zSum)
    (Eq.trans (Eq.cong (_+ - ₁₊ a2')
        (Eq.trans (Eq.sym (+-assoc (- ₁₊ a1') (₁₊ w + ₁₊ a2') (₁₊ a1')))
        (Eq.trans (Eq.cong (_+ ₁₊ a1')
            (+-comm (- ₁₊ a1') (₁₊ w + ₁₊ a2')))
        (Eq.trans (+-assoc (₁₊ w + ₁₊ a2') (- ₁₊ a1') (₁₊ a1'))
        (Eq.trans (Eq.cong ((₁₊ w + ₁₊ a2') +_) (+-inverseˡ (₁₊ a1')))
          (+-identityʳ (₁₊ w + ₁₊ a2')))))))
    (Eq.trans (+-assoc (₁₊ w) (₁₊ a2') (- ₁₊ a2'))
    (Eq.trans (Eq.cong (₁₊ w +_) (+-inverseʳ (₁₊ a2')))
      (+-identityʳ (₁₊ w)))))

  r6fix : - ₁₊ z + nsum p-1 (- ₁₊ w) ≡ - ₁₊ z + ₁₊ w
  r6fix = Eq.cong (- ₁₊ z +_) nfixw

  -- the two sides' second box agree: both are b2 - a₁ - w.
  d2fix : ∀ (b2 : ℤ ₚ) →
    (b2 + - ₁₊ a1') + - ₁₊ w ≡ (b2 + - ₁₊ z) + ₁₊ a2'
  d2fix b2 = Eq.sym
    (Eq.trans (Eq.cong (λ t → (b2 + t) + ₁₊ a2') negz)
    (Eq.trans (Eq.cong (_+ ₁₊ a2')
        (Eq.sym (+-assoc b2 (- ₁₊ w + - ₁₊ a2') (- ₁₊ a1'))))
    (Eq.trans (+-assoc (b2 + (- ₁₊ w + - ₁₊ a2')) (- ₁₊ a1') (₁₊ a2'))
    (Eq.trans (Eq.cong ((b2 + (- ₁₊ w + - ₁₊ a2')) +_)
        (+-comm (- ₁₊ a1') (₁₊ a2')))
    (Eq.trans (Eq.sym (+-assoc (b2 + (- ₁₊ w + - ₁₊ a2'))
        (₁₊ a2') (- ₁₊ a1')))
    (Eq.trans (Eq.cong (_+ - ₁₊ a1')
      (Eq.trans (+-assoc b2 (- ₁₊ w + - ₁₊ a2') (₁₊ a2'))
        (Eq.cong (b2 +_)
          (Eq.trans (+-assoc (- ₁₊ w) (- ₁₊ a2') (₁₊ a2'))
          (Eq.trans (Eq.cong (- ₁₊ w +_) (+-inverseˡ (₁₊ a2')))
            (+-identityʳ (- ₁₊ w)))))))
      (Eq.trans (+-assoc b2 (- ₁₊ w) (- ₁₊ a1'))
      (Eq.trans (Eq.cong (b2 +_) (+-comm (- ₁₊ w) (- ₁₊ a1')))
        (Eq.sym (+-assoc b2 (- ₁₊ a1') (- ₁₊ w)))))))))))

------------------------------------------------------------------------
-- The unit kit for the ββ branch (analogue of SrelWDSel10l.BAValues),
-- under zSum : z ≡ (w + a₂) + a₁.  This branch has four distinct units,
-- since neither box degenerates on either side.

module Units (a1' a2' w z : Fin (₁₊ p-2))
  (zSum : ₁₊ z ≡ (₁₊ w + ₁₊ a2') + ₁₊ a1') where

  A₁* A₂* W* Z* : ℤ* ₚ
  A₁* = (₁₊ a1' , λ ())
  A₂* = (₁₊ a2' , λ ())
  W*  = (₁₊ w , λ ())
  Z*  = (₁₊ z , λ ())

  iA₁ iA₂ iW iZ : ℤ ₚ
  iA₁ = (A₁* ⁻¹) .proj₁
  iA₂ = (A₂* ⁻¹) .proj₁
  iW  = (W* ⁻¹) .proj₁
  iZ  = (Z* ⁻¹) .proj₁

  -- the S-exponents in PADg, PADw and PADz
  u₁v v₁v uwv vwv uzv vzv : ℤ ₚ
  u₁v = - ₁₊ a2' * iA₁
  v₁v = - ₁₊ a1' * iA₂
  uwv = - ₁₊ a2' * iW
  vwv = - ₁₊ w   * iA₂
  uzv = - ₁₊ a2' * iZ
  vzv = - ₁₊ z   * iA₂

  negneg : ∀ (s t : ℤ ₚ) → - s * - t ≡ s * t
  negneg s t = Eq.trans (Eq.sym (-‿distribˡ-* s (- t)))
    (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* s t)))
      (-‿involutive (s * t)))

  zA : ₁₊ z + - ₁₊ a1' ≡ ₁₊ w + ₁₊ a2'
  zA = Eq.trans (Eq.cong (_+ - ₁₊ a1') zSum)
    (Eq.trans (+-assoc (₁₊ w + ₁₊ a2') (₁₊ a1') (- ₁₊ a1'))
    (Eq.trans (Eq.cong ((₁₊ w + ₁₊ a2') +_) (+-inverseʳ (₁₊ a1')))
      (+-identityʳ (₁₊ w + ₁₊ a2'))))

  zB : ₁₊ z + - ₁₊ a2' ≡ ₁₊ w + ₁₊ a1'
  zB = Eq.trans (Eq.cong (_+ - ₁₊ a2') zSum)
    (Eq.trans (Eq.cong (_+ - ₁₊ a2') (+-assoc (₁₊ w) (₁₊ a2') (₁₊ a1')))
    (Eq.trans (Eq.cong (λ t → (₁₊ w + t) + - ₁₊ a2')
        (+-comm (₁₊ a2') (₁₊ a1')))
    (Eq.trans (Eq.cong (_+ - ₁₊ a2')
        (Eq.sym (+-assoc (₁₊ w) (₁₊ a1') (₁₊ a2'))))
    (Eq.trans (+-assoc (₁₊ w + ₁₊ a1') (₁₊ a2') (- ₁₊ a2'))
    (Eq.trans (Eq.cong ((₁₊ w + ₁₊ a1') +_) (+-inverseʳ (₁₊ a2')))
      (+-identityʳ (₁₊ w + ₁₊ a1')))))))

------------------------------------------------------------------------
-- The ββ orbit.  Nothing degenerates: all four H escapes are clause-4
-- units and all four CZs are the padSA pad.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    RESTk RESTk3 RESTk4 : Word (Gen (₃₊ m))
    RESTk  = H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
    RESTk3 = CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑
    RESTk4 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

  module RStepsK (b1 b2 : ℤ ₚ) (a1' a2' w z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m))
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) where

    open Values a1' a2' w z b1 eqY eqZ public

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    E₁raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S ^ p-1)) .proj₁
    E₃raw = ((ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₁₊ z) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) S⁻¹) .proj₁

    PADg PADw PADz HU1 HU2 HU3 : Word (Gen (₂₊ m))
    PADg = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) CZ) .proj₁
    PADw = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ w , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ w * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑
        • (H ↑) ^ 3)))))
    PADz = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ z , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ z * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑
        • (H ↑) ^ 3)))))
    HU1 = Hdir (₁₊ a1' , ₁₊ w) ↓ᵏ (₁₊ m)
    HU2 = Hdir (₁₊ a1' , ₁₊ z) ↓ᵏ (₁₊ m)
    HU3 = Hdir (₁₊ z , ₁₊ w) ↓ᵏ (₁₊ m)

    ------------------------------------------------------------------
    -- coset side

    L-coset : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
                .proj₂
              ≡ inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
                  inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₁₊ w) , lm2))
    L-coset = Eq.trans
      (Eq.cong (λ v → ((ract2 ᵗ)
          (inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2))) CZ) .proj₂)
        eqY)
      (Eq.cong (λ v → inj₂ ((₁₊ w , v) ,
          inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₁₊ w) , lm2)))
        vfix)

    r1 : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↓))
         ≡ (E₁raw , inj₂ ((₁₊ a1' , ₁₊ z) , lm))
    r1 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) u)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , b1) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') b1 (λ ()))
              (Eq.cong (₁₊ a1' ,_) r1fix)))))

    r3 : ((ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) (S⁻¹ ↓))
         ≡ (E₃raw , inj₂ ((₁₊ z , - ₁₊ a1' + ₁₊ z) , lm))
    r3 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) u)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ z , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ z) (- ₁₊ a1') (λ ()))
              (Eq.cong (₁₊ z ,_) r3fix)))))

    r6 : ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₁₊ z) ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↓))
         ≡ (E₆raw , inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
             inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₁₊ w , - ₁₊ z) ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) u) (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ w , - ₁₊ z)
            (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)))
            (Eq.trans (it-dDS-nz p-1 (₁₊ w) (- ₁₊ z) (λ ()))
              (Eq.cong (₁₊ w ,_) r6fix)))))

    r7 : ((ract2 ᵗ) (inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↑))
         ≡ ((E₇raw ↑) , inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
             inj₂ ((₁₊ a2' , (b2 + - ₁₊ z) + ₁₊ a2') , lm2)))
    r7 = Eq.trans
      (ract-↑-≡ (₁₊ w , - ₁₊ z + ₁₊ w)
        (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₁₊ z) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₁₊ z) (λ ()))
                (Eq.cong (₁₊ a2' ,_)
                  (Eq.cong ((b2 + - ₁₊ z) +_) nfixa2)))))))

    R-coset : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
              ≡ inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
                  inj₂ ((₁₊ a2' , (b2 + - ₁₊ z) + ₁₊ a2') , lm2))
    R-coset =
      Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) (pr .proj₂) RESTk) .proj₂) r1)
      (Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) (pr .proj₂) RESTk3) .proj₂) r3)
      (Eq.trans (Eq.cong (λ v → ((ract2 ᵗ) (inj₂ ((₁₊ z , v) ,
                    inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) RESTk4) .proj₂)
                  r5fix)
      (Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂) r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (CZ • H ↓ • CZ)) .proj₂
             ≡ ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-coset
      (Eq.trans (Eq.cong (λ v → inj₂ ((₁₊ w , - ₁₊ z + ₁₊ w) ,
                    inj₂ ((₁₊ a2' , v) , lm2)))
                  (d2fix b2))
        (Eq.sym R-coset))

    ------------------------------------------------------------------
    -- residual side

    E₁≈ε : E₁raw ≈ ε
    E₁≈ε = ract-S^-resid-a+ (₁₊ a1' , b1) lm p-1 (λ ())

    E₃≈ε : E₃raw ≈ ε
    E₃≈ε = ract-S^-resid-a+ (₁₊ z , - ₁₊ a1') lm p-1 (λ ())

    E₆≈ε : E₆raw ≈ ε
    E₆≈ε = ract-S^-resid-a+ (₁₊ w , - ₁₊ z)
             (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) p-1 (λ ())

    E₇≈ε : E₇raw ↑ ≈ ε
    E₇≈ε = trans (lemma-cong↑ E₇raw ε
             (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₁₊ z) lm2 p-1 (λ ()))) refl

    L-pads : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
               .proj₁ ≡ PADg • (HU1 • PADw)
    L-pads = Eq.cong₂ _•_ Eq.refl
      (Eq.cong₂ _•_
        (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) eqY)
        (Eq.trans
          (Eq.cong (λ c → ((ract2 ᵗ) c CZ) .proj₁)
            (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
                inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
              eqY))
          (padSA w a2' (- ₁₊ a1') (b2 + - ₁₊ a1'))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
            ≡ E₁raw • (HU2 • (E₃raw • (PADz • (HU3 •
                (E₆raw • (E₇raw ↑))))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) RESTk) .proj₁) r1)
      (Eq.cong (E₁raw •_)
      (Eq.cong (HU2 •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) RESTk3) .proj₁) r3)
      (Eq.cong (E₃raw •_)
      (Eq.trans (Eq.cong₂ _•_
          (padSA z a2' (- ₁₊ a1' + ₁₊ z) b2) Eq.refl)
      (Eq.cong (PADz •_)
      (Eq.trans (Eq.cong
          (λ v → ((ract2 ᵗ) (inj₂ ((₁₊ z , v) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) RESTk4) .proj₁)
          r5fix)
      (Eq.cong (HU3 •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁) r6)
        (Eq.cong (E₆raw •_) (Eq.cong proj₁ r7)))))))))))

    Rclean : E₁raw • (HU2 • (E₃raw • (PADz • (HU3 •
               (E₆raw • (E₇raw ↑))))))
             ≈ HU2 • (PADz • HU3)
    Rclean = trans (cleft E₁≈ε) (trans left-unit
      (cright (trans (trans (cleft E₃≈ε) left-unit)
        (cright (trans (cright (trans (cleft E₆≈ε)
                        (trans left-unit E₇≈ε)))
                       right-unit)))))

    idββ-c11-Goal : Set
    idββ-c11-Goal = PADg • (HU1 • PADw) ≈ HU2 • (PADz • HU3)

  c11-go-aaββ : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    RStepsK.idββ-c11-Goal b1 b2 a1' a2' w z lm2 eqY eqZ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-aaββ b1 b2 a1' a2' w z lm2 eqY eqZ ident = resid≈ , coset≡
    where
    open RStepsK b1 b2 a1' a2' w z lm2 eqY eqZ

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ = trans (refl' L-pads)
      (trans ident (sym (trans (refl' R-fix) Rclean)))
