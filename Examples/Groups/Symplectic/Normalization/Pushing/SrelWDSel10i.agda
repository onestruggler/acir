------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₀,₁₊b2'), branch β: the orbit assembly.
-- The witness x = b₂ - a₁ drives the box walk; both clause-4 escapes
-- and the hpad unit are wired to idβ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10i
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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10h
  p-2 p-prime using (module XValues ; idβ)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  c10-go-a0bβ : ∀ (b1 : ℤ ₚ) (a1' b2' x : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    ₁₊ b2' + - ₁₊ a1' ≡ ₁₊ x →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-a0bβ b1 a1' b2' x lm2 eq-X = resid≈ , coset≡
    where
    open XValues a1' b2' x eq-X

    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , ₁₊ b2') , lm2)

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    PAD PAD' : Word (Gen (₂₊ m))
    PAD  = H • (H ↑ • (CZ • (S^ uv •
      (H ^ 3 • (S^ vv ↑ • (H ↑) ^ 3)))))
    PAD' = H • (H ↑ • (CZ • (S^ u'v •
      (H ^ 3 • (S^ v'v ↑ • (H ↑) ^ 3)))))

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    bfix3g : - ₀ + nsum p-1 (- ₁₊ b2') ≡ ₁₊ b2'
    bfix3g = Eq.trans (Eq.cong₂ _+_ -0#≈0#
        (Eq.trans (nsum-p-1 (- ₁₊ b2')) (-‿involutive (₁₊ b2'))))
      (+-identityˡ (₁₊ b2'))

    vβ6 : - ₁₊ b2' + nsum p-1 (- ₁₊ x) ≡ - ₁₊ a1'
    vβ6 = Eq.trans (Eq.cong (- ₁₊ b2' +_)
        (Eq.trans (nsum-p-1 (- ₁₊ x)) (-‿involutive (₁₊ x))))
      (Eq.trans (+-comm (- ₁₊ b2') (₁₊ x)) wXB)

    wNeg : - ₁₊ b2' + ₁₊ a1' ≡ - ₁₊ x
    wNeg = Eq.sym (Eq.trans (Eq.cong -_ (Eq.sym eq-X))
      (Eq.trans (Eq.sym (-‿+-comm (₁₊ b2') (- ₁₊ a1')))
        (Eq.cong (- ₁₊ b2' +_) (-‿involutive (₁₊ a1')))))

    r7β : (b1 + - ₁₊ b2') + nsum p-1 (- ₁₊ a1') ≡ b1 + - ₁₊ x
    r7β = Eq.trans (Eq.cong ((b1 + - ₁₊ b2') +_) nfixa1)
      (Eq.trans (+-assoc b1 (- ₁₊ b2') (₁₊ a1'))
        (Eq.cong (b1 +_) wNeg))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1 + - ₁₊ x) , inj₂ ((₁₊ x , - ₁₊ a1') , lm2))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            WD • (ε • PAD)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₀ , v) ↓ᵏ m) ↑) eq-X)
      (Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
          (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
              inj₂ (Hd' (₀ , v) , lm2)))
            eq-X))
        (padSA a1' x (b1 + - ₀) (- ₀))))

    L-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ (Hd' (₀ , v) , lm2)))
          eq-X))
      (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₁₊ x , u) , lm2)))
        (Eq.cong (_+ - ₁₊ x) (e0 b1))
        (Eq.trans (Eq.cong (_+ - ₁₊ a1') -0#≈0#)
          (+-identityˡ (- ₁₊ a1'))))

    -- RHS letters.
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹) .proj₁
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ x , - ₁₊ b2') , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
              inj₂ ((₁₊ x , - ₁₊ a1') , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1i : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) , lm))
    r1i = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (₁₊ b2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (₁₊ b2'))))))

    r3i : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ b2' , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          (E₃raw ↑ , inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ b2' , ₁₊ b2') , lm2)))
    r3i = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ b2' , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ b2') (- ₀) (λ ()))
                (Eq.cong (₁₊ b2' ,_) bfix3g))))))

    PADfixβ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
                inj₂ ((₁₊ b2' , ₁₊ b2') , lm2))) CZ) .proj₁ ≡ PAD'
    PADfixβ = padSA a1' b2' b1 (₁₊ b2')

    r5i : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ b2' , ₁₊ b2' + - ₁₊ a1') , lm2))) (H ↑)) ≡
          ((ZM q̂p • S^ r̂v) ↑ ,
           inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
             inj₂ ((₁₊ x , - ₁₊ b2') , lm2)))
    r5i = Eq.trans
      (Eq.cong (λ v → ((Hdir (₁₊ b2' , v) ↓ᵏ m) ↑ ,
          inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ (Hd' (₁₊ b2' , v) , lm2))))
        eq-X)
      (Eq.cong₂ _,_ (Eq.cong _↑ (hpad b2' x)) Eq.refl)

    r6i : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ x , - ₁₊ b2') , lm2))) (S⁻¹ ↑)) ≡
          (E₆raw ↑ , inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ x , - ₁₊ a1') , lm2)))
    r6i = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₁₊ b2')
        (inj₂ ((₁₊ x , - ₁₊ b2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') , c))
          (Eq.trans (ract-S^-coset (₁₊ x , - ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ x) (- ₁₊ b2') (λ ()))
                (Eq.cong (₁₊ x ,_) vβ6))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
              (E₃raw ↑ • (PAD' • ((ZM q̂p • S^ r̂v) ↑ •
                (E₆raw ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1i)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3i)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ PADfixβ Eq.refl)
      (Eq.cong (λ t → PAD' • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5i)
      (Eq.cong (λ t → (ZM q̂p • S^ r̂v) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6i)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ x , - ₁₊ a1') , lm2))) u) .proj₁)
          (↓-pow-S p-1))))))))))))

    Rclean : (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
               (E₃raw ↑ • (PAD' • ((ZM q̂p • S^ r̂v) ↑ •
                 (E₆raw ↑ • E₇raw))))) ≈
             S⁻¹ ↑ • (PAD' • (ZM q̂p ↑ • S^ r̂v ↑))
    Rclean =
      trans (cright left-unit)
      (trans (cright (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ b2' , - ₀) lm2 p-1 (λ ())))) left-unit))
             (cright (cright (trans (cright
          (trans (cleft (lemma-cong↑ E₆raw ε
            (ract-S^-resid-a+ (₁₊ x , - ₁₊ b2') lm2 p-1 (λ ()))))
          (trans left-unit
            (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₁₊ b2')
              (inj₂ ((₁₊ x , - ₁₊ a1') , lm2)) p-1 (λ ())))))
        right-unit))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (cright left-unit)
      (trans (idβ a1' b2' x eq-X)
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1i)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3i)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5i)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6i)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ x , - ₁₊ a1') , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₁₊ b2')
          (inj₂ ((₁₊ x , - ₁₊ a1') , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ x , - ₁₊ a1') , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₁₊ b2') (λ ())))
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , v) ,
            inj₂ ((₁₊ x , - ₁₊ a1') , lm2)))
          r7β)))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
