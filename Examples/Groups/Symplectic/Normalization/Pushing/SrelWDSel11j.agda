------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on (₁₊a1',b1)/(₁₊a2',b2), sub-case αβ.
--
-- Y = b₁ - a₂ vanishes and Z = b₁ + a₁ ≡ z, so b₁ ≡ a₂ and z ≡ a₂ + a₁.
-- The first CZ leaves the bottom box (A1, ₀), so the middle H escapes
-- HH and the second CZ meets an a=₀ box; on the R-side the leading S⁻¹
-- turns the bottom box to (A1, ₁₊ z) instead, so the escapes swap roles.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11j
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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

------------------------------------------------------------------------
-- The value kit.
--
--   eqY : b1 + - ₁₊ a2' ≡ ₀    (α on the first split)  ⇒ b1 ≡ a₂
--   eqZ : b1 + ₁₊ a1'  ≡ ₁₊ z  (β on the second)       ⇒ z ≡ a₂ + a₁

module Values (a1' a2' z : Fin (₁₊ p-2)) (b1 : ℤ ₚ)
  (eqY : b1 + - ₁₊ a2' ≡ ₀) (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) where

  b1A2 : b1 ≡ ₁₊ a2'
  b1A2 = Eq.trans (Eq.sym (+-identityʳ b1))
    (Eq.trans (Eq.cong (b1 +_) (Eq.sym (+-inverseˡ (₁₊ a2'))))
    (Eq.trans (Eq.sym (+-assoc b1 (- ₁₊ a2') (₁₊ a2')))
    (Eq.trans (Eq.cong (_+ ₁₊ a2') eqY) (+-identityˡ (₁₊ a2')))))

  zSum : ₁₊ z ≡ ₁₊ a2' + ₁₊ a1'
  zSum = Eq.trans (Eq.sym eqZ) (Eq.cong (_+ ₁₊ a1') b1A2)

  negz : - ₁₊ z ≡ - ₁₊ a2' + - ₁₊ a1'
  negz = Eq.trans (Eq.cong -_ zSum)
    (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ a1')))

  -- the bottom box's b after the second CZ
  vfix : - ₁₊ a1' + - ₁₊ a2' ≡ - ₁₊ z
  vfix = Eq.trans (+-comm (- ₁₊ a1') (- ₁₊ a2')) (Eq.sym negz)

  nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
  nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

  nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
  nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

  nfixz : nsum p-1 (- ₁₊ z) ≡ ₁₊ z
  nfixz = Eq.trans (nsum-p-1 (- ₁₊ z)) (-‿involutive (₁₊ z))

  e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
  e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

  -- R-side step 1: the leading S⁻¹ turns the bottom box to (A1, ₁₊ z).
  r1fix : b1 + nsum p-1 (- ₁₊ a1') ≡ ₁₊ z
  r1fix = Eq.trans (Eq.cong (b1 +_) nfixa1) eqZ

  -- R-side step 3: S⁻¹ on the (₁₊ z, -A1) box.
  r3fix : - ₁₊ a1' + nsum p-1 (- ₁₊ z) ≡ - ₁₊ a1' + ₁₊ z
  r3fix = Eq.cong (- ₁₊ a1' +_) nfixz

  -- R-side step 5: the bottom box's b vanishes, so H sees (₁₊ z , ₀).
  r5fix : (- ₁₊ a1' + ₁₊ z) + - ₁₊ a2' ≡ ₀
  r5fix = Eq.trans (Eq.cong (λ t → (- ₁₊ a1' + t) + - ₁₊ a2') zSum)
    (Eq.trans (Eq.cong (_+ - ₁₊ a2')
        (Eq.trans (Eq.sym (+-assoc (- ₁₊ a1') (₁₊ a2') (₁₊ a1')))
        (Eq.trans (Eq.cong (_+ ₁₊ a1') (+-comm (- ₁₊ a1') (₁₊ a2')))
        (Eq.trans (+-assoc (₁₊ a2') (- ₁₊ a1') (₁₊ a1'))
        (Eq.trans (Eq.cong (₁₊ a2' +_) (+-inverseˡ (₁₊ a1')))
          (+-identityʳ (₁₊ a2')))))))
      (+-inverseʳ (₁₊ a2')))

  -- the two sides' second box agree: both are b2 - a₁.
  d2fix : ∀ (b2 : ℤ ₚ) → (b2 + - ₁₊ a1') + - ₀ ≡ (b2 + - ₁₊ z) + ₁₊ a2'
  d2fix b2 = Eq.trans (e0 (b2 + - ₁₊ a1'))
    (Eq.sym (Eq.trans (Eq.cong (λ t → (b2 + t) + ₁₊ a2') negz)
    (Eq.trans (Eq.cong (_+ ₁₊ a2')
        (Eq.sym (+-assoc b2 (- ₁₊ a2') (- ₁₊ a1'))))
    (Eq.trans (+-assoc (b2 + - ₁₊ a2') (- ₁₊ a1') (₁₊ a2'))
    (Eq.trans (Eq.cong ((b2 + - ₁₊ a2') +_) (+-comm (- ₁₊ a1') (₁₊ a2')))
    (Eq.trans (Eq.sym (+-assoc (b2 + - ₁₊ a2') (₁₊ a2') (- ₁₊ a1')))
      (Eq.cong (_+ - ₁₊ a1')
        (Eq.trans (+-assoc b2 (- ₁₊ a2') (₁₊ a2'))
        (Eq.trans (Eq.cong (b2 +_) (+-inverseˡ (₁₊ a2')))
          (+-identityʳ b2))))))))))

------------------------------------------------------------------------
-- The coset half.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  -- LHS: CZ leaves (A1, ₀), H turns it to (₀, -A1), the second CZ
  -- couples it to (A2, b2 - A1).
  c11-αβ-L-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₀) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) .proj₂
    ≡ inj₂ ((₀ , - ₁₊ z) ,
        inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₀) , lm2))
  c11-αβ-L-coset b1 b2 a1' a2' z lm2 eqY eqZ =
    Eq.trans
      (Eq.cong (λ v → ((ract2 ᵗ)
          (inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2))) CZ) .proj₂)
        eqY)
      (Eq.cong (λ v → inj₂ ((₀ , v) ,
          inj₂ ((₁₊ a2' , (b2 + - ₁₊ a1') + - ₀) , lm2)))
        (Values.vfix a1' a2' z b1 eqY eqZ))

  private
    RESTj : Word (Gen (₃₊ m))
    RESTj = H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    RESTj3 : Word (Gen (₃₊ m))
    RESTj3 = CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    RESTj4 : Word (Gen (₃₊ m))
    RESTj4 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

  -- RHS: the leading S⁻¹ makes the bottom box (A1, ₁₊ z) instead, so H
  -- turns it to (₁₊ z, -A1); after the CZ its b vanishes (r5fix) and the
  -- second H drops it to (₀, -₁₊ z).
  c11-αβ-R-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₀) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    ≡ inj₂ ((₀ , - ₁₊ z) ,
        inj₂ ((₁₊ a2' , (b2 + - ₁₊ z) + ₁₊ a2') , lm2))
  c11-αβ-R-coset b1 b2 a1' a2' z lm2 eqY eqZ =
    Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c RESTj) .proj₂) s1)
    (Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c RESTj3) .proj₂) s3)
    (Eq.trans (Eq.cong (λ v → ((ract2 ᵗ)
                  (inj₂ ((₁₊ z , v) ,
                    inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) RESTj4) .proj₂)
                r5fix)
              s7))
    where
    open Values a1' a2' z b1 eqY eqZ

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    s1 : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↓)) .proj₂
         ≡ inj₂ ((₁₊ a1' , ₁₊ z) , lm)
    s1 = Eq.trans
      (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) u) .proj₂)
        (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1) lm p-1)
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz p-1 (₁₊ a1') b1 (λ ()))
            (Eq.cong (₁₊ a1' ,_) r1fix))))

    s3 : ((ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) (S⁻¹ ↓)) .proj₂
         ≡ inj₂ ((₁₊ z , - ₁₊ a1' + ₁₊ z) , lm)
    s3 = Eq.trans
      (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) u) .proj₂)
        (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ z , - ₁₊ a1') lm p-1)
        (Eq.cong (λ d → inj₂ (d , lm))
          (Eq.trans (it-dDS-nz p-1 (₁₊ z) (- ₁₊ a1') (λ ()))
            (Eq.cong (₁₊ z ,_) r3fix))))

    s7 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
         ≡ inj₂ ((₀ , - ₁₊ z) ,
             inj₂ ((₁₊ a2' , (b2 + - ₁₊ z) + ₁₊ a2') , lm2))
    s7 = Eq.trans (Eq.cong (λ c → ((ract2 ᵗ) c (S⁻¹ ↑)) .proj₂) s6) s7'
      where
      s6 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
             inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↓)) .proj₂
           ≡ inj₂ ((₀ , - ₁₊ z) ,
               inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))
      s6 = Eq.trans
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
            inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ z)
            (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)))
            (it-dDS-a0 p-1 (- ₁₊ z))))

      s7' : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↑)) .proj₂
            ≡ inj₂ ((₀ , - ₁₊ z) ,
                inj₂ ((₁₊ a2' , (b2 + - ₁₊ z) + ₁₊ a2') , lm2))
      s7' = Eq.trans
        (Eq.cong proj₂ (ract-↑-≡ (₀ , - ₁₊ z)
          (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) S⁻¹))
        (Eq.cong (λ c → inj₂ ((₀ , - ₁₊ z) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2 + - ₁₊ z) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (b2 + - ₁₊ z) (λ ()))
                (Eq.cong (₁₊ a2' ,_)
                  (Eq.cong ((b2 + - ₁₊ z) +_) nfixa2))))))

  c11-αβ-coset : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₀) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) .proj₂
    ≡ ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
  c11-αβ-coset b1 b2 a1' a2' z lm2 eqY eqZ =
    Eq.trans (c11-αβ-L-coset b1 b2 a1' a2' z lm2 eqY eqZ)
    (Eq.trans (Eq.cong (λ v → inj₂ ((₀ , - ₁₊ z) ,
                  inj₂ ((₁₊ a2' , v) , lm2)))
                (Values.d2fix a1' a2' z b1 eqY eqZ b2))
      (Eq.sym (c11-αβ-R-coset b1 b2 a1' a2' z lm2 eqY eqZ)))

------------------------------------------------------------------------
-- The residual side.

  module RStepsJ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m))
    (eqY : b1 + - ₁₊ a2' ≡ ₀) (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) where

    open Values a1' a2' z b1 eqY eqZ public

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    E₁raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S ^ p-1)) .proj₁
    E₃raw = ((ract2 ᵗ) (inj₂ ((₁₊ z , - ₁₊ a1') , lm)) (S ^ p-1)) .proj₁
    E₇raw = ((ract {₁₊ m} ᵗ)
              (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) S⁻¹) .proj₁

    PADg : Word (Gen (₂₊ m))
    PADg = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) CZ) .proj₁

    HH2 HU HHz CZpadA PADz : Word (Gen (₂₊ m))
    HH2 = Hdir (₁₊ a1' , ₀) ↓ᵏ (₁₊ m)
    HU  = Hdir (₁₊ a1' , ₁₊ z) ↓ᵏ (₁₊ m)
    HHz = Hdir (₁₊ z , ₀) ↓ᵏ (₁₊ m)
    CZpadA = ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ a1') ,
               inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2))) CZ) .proj₁
    PADz = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ z , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ z * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑
        • (H ↑) ^ 3)))))

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

    r6 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↓))
         ≡ ((S ^ p-1) , inj₂ ((₀ , - ₁₊ z) ,
             inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ u → (ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
          inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) u) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ z)
          (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ z)
            (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)))
            (it-dDS-a0 p-1 (- ₁₊ z)))))

    r7 : ((ract2 ᵗ) (inj₂ ((₀ , - ₁₊ z) ,
           inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) (S⁻¹ ↑)) .proj₁
         ≡ E₇raw ↑
    r7 = Eq.cong proj₁ (ract-↑-≡ (₀ , - ₁₊ z)
           (inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2)) S⁻¹)

    E₁≈ε : E₁raw ≈ ε
    E₁≈ε = ract-S^-resid-a+ (₁₊ a1' , b1) lm p-1 (λ ())

    E₃≈ε : E₃raw ≈ ε
    E₃≈ε = ract-S^-resid-a+ (₁₊ z , - ₁₊ a1') lm p-1 (λ ())

    E₇≈ε : E₇raw ↑ ≈ ε
    E₇≈ε = trans (lemma-cong↑ E₇raw ε
             (ract-S^-resid-a+ (₁₊ a2' , b2 + - ₁₊ z) lm2 p-1 (λ ()))) refl

    L-pads : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↓ • CZ))
               .proj₁ ≡ PADg • (HH2 • CZpadA)
    L-pads = Eq.cong₂ _•_ Eq.refl
      (Eq.cong₂ _•_
        (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) eqY)
        (Eq.cong (λ c → ((ract2 ᵗ) c CZ) .proj₁)
          (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ a1') , lm2)))
            eqY)))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
            ≡ E₁raw • (HU • (E₃raw • (PADz • (HHz •
                ((S ^ p-1) • (E₇raw ↑))))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) RESTj) .proj₁) r1)
      (Eq.cong (E₁raw •_)
      (Eq.cong (HU •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) RESTj3) .proj₁) r3)
      (Eq.cong (E₃raw •_)
      (Eq.trans (Eq.cong₂ _•_
          (padSA z a2' (- ₁₊ a1' + ₁₊ z) b2) Eq.refl)
      (Eq.cong (PADz •_)
      (Eq.trans (Eq.cong
          (λ v → ((ract2 ᵗ) (inj₂ ((₁₊ z , v) ,
              inj₂ ((₁₊ a2' , b2 + - ₁₊ z) , lm2))) RESTj4) .proj₁)
          r5fix)
      (Eq.cong (HHz •_)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁) r6)
        (Eq.cong ((S ^ p-1) •_) r7))))))))))

    Rclean : E₁raw • (HU • (E₃raw • (PADz • (HHz •
               ((S ^ p-1) • (E₇raw ↑))))))
             ≈ HU • (PADz • (HHz • (S ^ p-1)))
    Rclean = trans (cleft E₁≈ε) (trans left-unit
      (cright (trans (trans (cleft E₃≈ε) left-unit)
        (cright (cright (trans (cright E₇≈ε) right-unit))))))

    idαβ-c11-Goal : Set
    idαβ-c11-Goal =
      PADg • (HH2 • CZpadA) ≈ HU • (PADz • (HHz • (S ^ p-1)))

  c11-go-aaαβ : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₀) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    RStepsJ.idαβ-c11-Goal b1 b2 a1' a2' z lm2 eqY eqZ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-aaαβ b1 b2 a1' a2' z lm2 eqY eqZ ident =
    resid≈ , c11-αβ-coset b1 b2 a1' a2' z lm2 eqY eqZ
    where
    open RStepsJ b1 b2 a1' a2' z lm2 eqY eqZ

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ = trans (refl' L-pads)
      (trans ident (sym (trans (refl' R-fix) Rclean)))
