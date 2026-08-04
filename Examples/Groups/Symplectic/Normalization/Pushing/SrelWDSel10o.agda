------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case ββ: the orbit.
-- Both shifted slots are nonzero (witnesses y and z), so each side
-- collects two clause-4 pads around hpad units and the residual is
-- idββ.  This closes the last sub-case of selinger-c10.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10o
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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  p-2 p-prime using (module BBValues ; idββ)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  c10-go-aaββ : ∀ (b1 b2 : ℤ ₚ) (a1' a2' y z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    b2 + - ₁₊ a1' ≡ ₁₊ y → b2 + ₁₊ a2' ≡ ₁₊ z →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-aaββ b1 b2 a1' a2' y z lm2 eq-Y eq-Z = resid≈ , coset≡
    where
    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    b2fromY : b2 ≡ ₁₊ y + ₁₊ a1'
    b2fromY = Eq.trans (Eq.sym (+-identityʳ b2))
      (Eq.trans (Eq.cong (b2 +_) (Eq.sym (+-inverseˡ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc b2 (- ₁₊ a1') (₁₊ a1')))
        (Eq.cong (_+ ₁₊ a1') eq-Y)))

    zySum : ₁₊ z ≡ ₁₊ y + (₁₊ a2' + ₁₊ a1')
    zySum = Eq.trans (Eq.sym eq-Z)
      (Eq.trans (Eq.cong (_+ ₁₊ a2') b2fromY)
      (Eq.trans (+-assoc (₁₊ y) (₁₊ a1') (₁₊ a2'))
        (Eq.cong (₁₊ y +_) (+-comm (₁₊ a1') (₁₊ a2')))))

    open BBValues a1' a2' y z zySum using (Qy* ; Qz* ; Qzy* ; iA₂ ; iZ)

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    nfixy : nsum p-1 (- ₁₊ y) ≡ ₁₊ y
    nfixy = Eq.trans (nsum-p-1 (- ₁₊ y)) (-‿involutive (₁₊ y))

    nfixz : nsum p-1 (- ₁₊ z) ≡ ₁₊ z
    nfixz = Eq.trans (nsum-p-1 (- ₁₊ z)) (-‿involutive (₁₊ z))

    negZ : - ₁₊ z ≡ - ₁₊ y + (- ₁₊ a2' + - ₁₊ a1')
    negZ = Eq.trans (Eq.cong -_ zySum)
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ y) (₁₊ a2' + ₁₊ a1')))
        (Eq.cong (- ₁₊ y +_) (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ a1')))))

    r1fix : b2 + nsum p-1 (- ₁₊ a2') ≡ ₁₊ z
    r1fix = Eq.trans (Eq.cong (b2 +_) nfixa2) eq-Z

    r3fix : - ₁₊ a2' + nsum p-1 (- ₁₊ z) ≡ b2
    r3fix = Eq.trans (Eq.cong (- ₁₊ a2' +_) nfixz)
      (Eq.trans (Eq.cong (- ₁₊ a2' +_) (Eq.sym eq-Z))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a2') b2 (₁₊ a2')))
      (Eq.trans (Eq.cong (_+ ₁₊ a2') (+-comm (- ₁₊ a2') b2))
      (Eq.trans (+-assoc b2 (- ₁₊ a2') (₁₊ a2'))
      (Eq.trans (Eq.cong (b2 +_) (+-inverseˡ (₁₊ a2')))
        (+-identityʳ b2))))))

    r6fix : - ₁₊ z + nsum p-1 (- ₁₊ y) ≡ - ₁₊ a2' + - ₁₊ a1'
    r6fix = Eq.trans (Eq.cong₂ _+_ negZ nfixy)
      (Eq.trans (+-comm (- ₁₊ y + (- ₁₊ a2' + - ₁₊ a1')) (₁₊ y))
      (Eq.trans (Eq.sym (+-assoc (₁₊ y) (- ₁₊ y)
          (- ₁₊ a2' + - ₁₊ a1')))
      (Eq.trans (Eq.cong (_+ (- ₁₊ a2' + - ₁₊ a1'))
          (+-inverseʳ (₁₊ y)))
        (+-identityˡ (- ₁₊ a2' + - ₁₊ a1')))))

    r7fix : (b1 + - ₁₊ z) + nsum p-1 (- ₁₊ a1') ≡
            (b1 + - ₁₊ a2') + - ₁₊ y
    r7fix = Eq.trans (Eq.cong ((b1 + - ₁₊ z) +_) nfixa1)
      (Eq.trans (+-assoc b1 (- ₁₊ z) (₁₊ a1'))
      (Eq.trans (Eq.cong (b1 +_) inner)
        (Eq.sym (+-assoc b1 (- ₁₊ a2') (- ₁₊ y)))))
      where
      inner : - ₁₊ z + ₁₊ a1' ≡ - ₁₊ a2' + - ₁₊ y
      inner = Eq.trans (Eq.cong (_+ ₁₊ a1') negZ)
        (Eq.trans (+-assoc (- ₁₊ y) (- ₁₊ a2' + - ₁₊ a1') (₁₊ a1'))
        (Eq.trans (Eq.cong (- ₁₊ y +_)
            (+-assoc (- ₁₊ a2') (- ₁₊ a1') (₁₊ a1')))
        (Eq.trans (Eq.cong (λ t → - ₁₊ y + (- ₁₊ a2' + t))
            (+-inverseˡ (₁₊ a1')))
        (Eq.trans (Eq.cong (- ₁₊ y +_) (+-identityʳ (- ₁₊ a2')))
          (+-comm (- ₁₊ y) (- ₁₊ a2'))))))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , (b1 + - ₁₊ a2') + - ₁₊ y) ,
          inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2))

    PADw : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    PADw u v = H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3)))))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            PADw (- ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                 (- ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) •
              ((ZM Qy* • S^ (₁₊ y * iA₂)) ↑ •
                PADw (- ₁₊ y * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                     (- ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁))
    L-fix = Eq.cong₂ _•_ (padSA a1' a2' b1 b2) (Eq.cong₂ _•_
      (Eq.trans (Eq.cong (λ v → (Hdir (₁₊ a2' , v) ↓ᵏ m) ↑) eq-Y)
        (Eq.cong _↑ (hpad a2' y)))
      (Eq.trans (Eq.cong (λ v → ((ract2 ᵗ)
            (inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') ,
              inj₂ (Hd' (₁₊ a2' , v) , lm2))) CZ) .proj₁)
          eq-Y)
        (padSA a1' y (b1 + - ₁₊ a2') (- ₁₊ a2'))))

    L-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.cong (λ v → ((ract2 ᵗ)
        (inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') ,
          inj₂ (Hd' (₁₊ a2' , v) , lm2))) CZ) .proj₂)
      eq-Y

    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , b2) , lm2)) S⁻¹) .proj₁
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ z , - ₁₊ a2') , lm2)) S⁻¹) .proj₁
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ y , - ₁₊ z) , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
              inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1o : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          (E₁raw ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , ₁₊ z) , lm2)))
    r1o = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') b2 (λ ()))
                (Eq.cong (₁₊ a2' ,_) r1fix))))))

    r3o : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ z , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
          (E₃raw ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ z , b2) , lm2)))
    r3o = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₁₊ z , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ z , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ z) (- ₁₊ a2') (λ ()))
                (Eq.cong (₁₊ z ,_) r3fix))))))

    r5o : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₁₊ z , b2 + - ₁₊ a1') , lm2))) (H ↑)) ≡
          ((ZM Qzy* • S^ (₁₊ y * iZ)) ↑ ,
           inj₂ ((₁₊ a1' , b1 + - ₁₊ z) , inj₂ ((₁₊ y , - ₁₊ z) , lm2)))
    r5o = Eq.trans
      (Eq.cong (λ v → ((Hdir (₁₊ z , v) ↓ᵏ m) ↑ ,
          inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ (Hd' (₁₊ z , v) , lm2))))
        eq-Y)
      (Eq.cong₂ _,_ (Eq.cong _↑ (hpad z y)) Eq.refl)

    r6o : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₁₊ y , - ₁₊ z) , lm2))) (S⁻¹ ↑)) ≡
          (E₆raw ↑ , inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2)))
    r6o = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₁₊ z) (inj₂ ((₁₊ y , - ₁₊ z) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₁₊ z) , c))
          (Eq.trans (ract-S^-coset (₁₊ y , - ₁₊ z) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ y) (- ₁₊ z) (λ ()))
                (Eq.cong (₁₊ y ,_) r6fix))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((ZM Qz* • S^ (₁₊ z * iA₂)) ↑ • (E₃raw ↑ •
              (PADw (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                    (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹) .proj₁) •
                ((ZM Qzy* • S^ (₁₊ y * iZ)) ↑ • (E₆raw ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1o)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ (Eq.cong _↑ (hpad a2' z)) Eq.refl)
      (Eq.cong (λ t → (ZM Qz* • S^ (₁₊ z * iA₂)) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3o)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ (padSA a1' z b1 b2) Eq.refl)
      (Eq.cong (λ t → PADw (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                           (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹) .proj₁) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5o)
      (Eq.cong (λ t → (ZM Qzy* • S^ (₁₊ y * iZ)) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6o)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
            inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2))) u) .proj₁)
          (↓-pow-S p-1)))))))))))))

    Rclean : E₁raw ↑ • ((ZM Qz* • S^ (₁₊ z * iA₂)) ↑ • (E₃raw ↑ •
               (PADw (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                     (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹) .proj₁) •
                 ((ZM Qzy* • S^ (₁₊ y * iZ)) ↑ • (E₆raw ↑ • E₇raw))))) ≈
             (ZM Qz* ↑ • S^ (₁₊ z * iA₂) ↑) •
               (PADw (- ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
                     (- ₁₊ a1' * ((₁₊ z , λ ()) ⁻¹) .proj₁) •
                 (ZM Qzy* ↑ • S^ (₁₊ y * iZ) ↑))
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , b2) lm2 p-1 (λ ())))) left-unit)
      (cright (trans (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ z , - ₁₊ a2') lm2 p-1 (λ ()))))
          left-unit)
        (cright (trans (cright
            (trans (cleft (lemma-cong↑ E₆raw ε
              (ract-S^-resid-a+ (₁₊ y , - ₁₊ z) lm2 p-1 (λ ()))))
            (trans left-unit
              (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₁₊ z)
                (inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2)) p-1
                (λ ())))))
          right-unit))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (idββ a1' a2' y z zySum)
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1o)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3o)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5o)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6o)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ)
            (inj₂ ((₁₊ a1' , b1 + - ₁₊ z) ,
              inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₁₊ z)
          (inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d ,
            inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₁₊ z) (λ ())))
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , v) ,
            inj₂ ((₁₊ y , - ₁₊ a2' + - ₁₊ a1') , lm2)))
          r7fix)))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
               .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
