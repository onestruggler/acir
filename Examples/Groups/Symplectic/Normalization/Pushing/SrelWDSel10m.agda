------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case βα: the orbit.
-- Z = b₂ + a₂ vanishes and Y = b₂ - a₁ ≡ y, so y ≡ -(a₂ + a₁); the
-- L-side collects two clause-4 pads around the a₂/y unit and the
-- R-side degenerates (its middle H↑ escapes ε), meeting at idβα.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10m
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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10l
  p-2 p-prime using (module BAValues ; idβα)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

  c10-go-aaβα : ∀ (b1 b2 : ℤ ₚ) (a1' a2' y : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    b2 + - ₁₊ a1' ≡ ₁₊ y → b2 + ₁₊ a2' ≡ ₀ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , b2) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-aaβα b1 b2 a1' a2' y lm2 eq-Y eq-Z = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , b2) , lm2)

    beqZ : b2 ≡ - ₁₊ a2'
    beqZ = Eq.trans (Eq.sym (+-identityʳ b2))
      (Eq.trans (Eq.cong (b2 +_) (Eq.sym (+-inverseʳ (₁₊ a2'))))
      (Eq.trans (Eq.sym (+-assoc b2 (₁₊ a2') (- ₁₊ a2')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a2') eq-Z)
        (+-identityˡ (- ₁₊ a2')))))

    ySum : ₁₊ y ≡ - (₁₊ a2' + ₁₊ a1')
    ySum = Eq.trans (Eq.sym eq-Y)
      (Eq.trans (Eq.cong (_+ - ₁₊ a1') beqZ)
        (-‿+-comm (₁₊ a2') (₁₊ a1')))

    open BAValues a1' a2' y ySum using (qŷp ; rŷv)

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixa2 : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa2 = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    nfixy : nsum p-1 (- ₁₊ y) ≡ ₁₊ y
    nfixy = Eq.trans (nsum-p-1 (- ₁₊ y)) (-‿involutive (₁₊ y))

    vfix : - ₁₊ a2' + - ₁₊ a1' ≡ ₁₊ y
    vfix = Eq.sym (Eq.trans ySum
      (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ a1'))))

    negy : - ₁₊ y ≡ ₁₊ a2' + ₁₊ a1'
    negy = Eq.trans (Eq.cong -_ ySum) (-‿involutive (₁₊ a2' + ₁₊ a1'))

    r1fix : b2 + nsum p-1 (- ₁₊ a2') ≡ ₀
    r1fix = Eq.trans (Eq.cong (b2 +_) nfixa2) eq-Z

    r6fix : - ₀ + nsum p-1 (- ₁₊ y) ≡ ₁₊ y
    r6fix = Eq.trans (Eq.cong₂ _+_ -0#≈0# nfixy) (+-identityˡ (₁₊ y))

    r7fix : (b1 + - ₀) + nsum p-1 (- ₁₊ a1') ≡ b1 + ₁₊ a1'
    r7fix = Eq.cong₂ _+_ (e0 b1) nfixa1

    d1fix : (b1 + - ₁₊ a2') + - ₁₊ y ≡ b1 + ₁₊ a1'
    d1fix = Eq.trans (Eq.cong ((b1 + - ₁₊ a2') +_) negy)
      (Eq.trans (+-assoc b1 (- ₁₊ a2') (₁₊ a2' + ₁₊ a1'))
      (Eq.trans (Eq.cong (b1 +_)
          (Eq.sym (+-assoc (- ₁₊ a2') (₁₊ a2') (₁₊ a1'))))
      (Eq.trans (Eq.cong (λ t → b1 + (t + ₁₊ a1'))
          (+-inverseˡ (₁₊ a2')))
        (Eq.cong (b1 +_) (+-identityˡ (₁₊ a1'))))))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1 + ₁₊ a1') , inj₂ ((₁₊ y , ₁₊ y) , lm2))

    PADgw PADyw : Word (Gen (₂₊ m))
    PADgw = H • (H ↑ • (CZ • (S^ (- ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁) ↑ •
        (H ↑) ^ 3)))))
    PADyw = H • (H ↑ • (CZ • (S^ (- ₁₊ y * ((₁₊ a1' , λ ()) ⁻¹) .proj₁)
      • (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁) ↑ •
        (H ↑) ^ 3)))))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            PADgw • ((ZM qŷp • S^ rŷv) ↑ • PADyw)
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
    L-c = Eq.trans (Eq.cong (λ v → ((ract2 ᵗ)
          (inj₂ ((₁₊ a1' , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2))) CZ) .proj₂)
        eq-Y)
      (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₁₊ y , u) , lm2)))
        d1fix
        vfix)

    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , b2) , lm2)) S⁻¹) .proj₁
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ y , - ₀) , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
              inj₂ ((₁₊ y , ₁₊ y) , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1m : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          (E₁raw ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₁₊ a2' , ₀) , lm2)))
    r1m = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , b2) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') b2 (λ ()))
                (Eq.cong (₁₊ a2' ,_) r1fix))))))

    r3m : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₀ , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₀ , - ₁₊ a2') , lm2)))
    r3m = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₀ , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₁₊ a2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (- ₁₊ a2'))))))

    r5m : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₁₊ a2' + - ₁₊ a1') , lm2))) (H ↑)) ≡
          (ε , inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ ((₁₊ y , - ₀) , lm2)))
    r5m = Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ m) ↑ ,
        inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2))))
      vfix

    r6m : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          (E₆raw ↑ , inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2)))
    r6m = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₀) (inj₂ ((₁₊ y , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₀) , c))
          (Eq.trans (ract-S^-coset (₁₊ y , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ y) (- ₀) (λ ()))
                (Eq.cong (₁₊ y ,_) r6fix))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((H ↑ • H ↑) • ((S ^ p-1) ↑ • (WD •
              (ε • (E₆raw ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1m)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.cong (λ t → (H ↑ • H ↑) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3m)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → WD • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5m)
      (Eq.cong (λ t → ε • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6m)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2))) u) .proj₁)
          (↓-pow-S p-1)))))))))))

    Rclean : E₁raw ↑ • ((H ↑ • H ↑) • ((S ^ p-1) ↑ • (WD •
               (ε • (E₆raw ↑ • E₇raw))))) ≈
             (H ↑ • H ↑) • (S⁻¹ ↑ • WD)
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , b2) lm2 p-1 (λ ())))) left-unit)
      (cright (cright (trans (cright (trans left-unit
          (trans (cleft (lemma-cong↑ E₆raw ε
            (ract-S^-resid-a+ (₁₊ y , - ₀) lm2 p-1 (λ ()))))
          (trans left-unit
            (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₀)
              (inj₂ ((₁₊ y , ₁₊ y) , lm2)) p-1 (λ ()))))))
        right-unit)))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (idβα a1' a2' y ySum)
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1m)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3m)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5m)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6m)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₀)
          (inj₂ ((₁₊ y , ₁₊ y) , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ y , ₁₊ y) , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₀) (λ ())))
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , v) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2)))
          r7fix)))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
               .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
