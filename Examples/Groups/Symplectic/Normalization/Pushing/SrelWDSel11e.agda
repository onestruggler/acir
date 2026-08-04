------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₁₊a1',₀)/(₀,b2).  Both CZ's are
-- bottom-conjugated, the two middle H's escape as HH, and the only
-- non-trivial escape is the diagonal unit S.  What is left is TW2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11e
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
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (TW2 ; H5 ; unitS)

------------------------------------------------------------------------
-- The residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid

  private
    WDe : Word (Gen (₂₊ m))
    WDe = H • (CZ • H ^ 3)

    fixdown11e : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdown11e = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  id11e : WDe • (HH • CZ) ≈ S • (WDe • (HH • (S⁻¹ • S⁻¹ ↑)))
  id11e = begin
    WDe • (HH • CZ)
      ≈⟨ trans assoc (cright assoc) ⟩
    H • (CZ • (H ^ 3 • (HH • CZ)))
      ≈⟨ cright (cright (trans (sym assoc) (cleft H5))) ⟩
    H • (CZ • (H • CZ))
      ≈⟨ cright (trans (axiom selinger-c11) (refl' fixdown11e)) ⟩
    H • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))))
      ≈⟨ trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc)) (sym assoc)) ⟩
    (H • (S⁻¹ • (H • S⁻¹))) • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))
      ≈⟨ cleft TW2 ⟩
    (S • H) • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))
      ≈⟨ assoc ⟩
    S • (H • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))
      ≈⟨ cright (cright (cright (trans (cleft (sym H5)) assoc))) ⟩
    S • (H • (CZ • (H ^ 3 • (HH • (S⁻¹ • S⁻¹ ↑)))))
      ≈⟨ sym (cright (trans assoc (cright assoc))) ⟩
    S • (WDe • (HH • (S⁻¹ • S⁻¹ ↑))) ∎

------------------------------------------------------------------------
-- The orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    WDe' : Word (Gen (₂₊ m))
    WDe' = H • (CZ • H ^ 3)

  c11-go-a00 : ∀ (b2 : ℤ ₚ) (a1' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-a00 b2 a1' lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    bf1 : ₀ + nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    bf1 = Eq.trans (Eq.cong (₀ +_) nfixa1) (+-identityˡ (₁₊ a1'))

    bf3 : - ₁₊ a1' + nsum p-1 (- ₁₊ a1') ≡ ₀
    bf3 = Eq.trans (Eq.cong (- ₁₊ a1' +_) nfixa1) (+-inverseˡ (₁₊ a1'))

    cF : C (₃₊ m)
    cF = inj₂ ((₀ , - ₁₊ a1') , inj₂ ((₀ , b2 + - ₁₊ a1') , lm2))

    -- LHS.
    L-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡ WDe' • (HH • CZ)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) (e0 ₀))
      (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 ₀))))

    L-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 ₀)))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        (e0 (- ₁₊ a1')) (e0 (b2 + - ₁₊ a1')))

    -- RHS.
    E₁raw = ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm)) (S ^ p-1)) .proj₁
    E₃raw = ((ract3 ᵗ) (inj₂ ((₁₊ a1' , - ₁₊ a1') , lm)) (S ^ p-1))
              .proj₁

    REST5e = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    r1 : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm)) (S⁻¹ ↓)) ≡
         (E₁raw , inj₂ ((₁₊ a1' , ₁₊ a1') , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') ₀ (λ ()))
              (Eq.cong (₁₊ a1' ,_) bf1)))))

    r3 : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , - ₁₊ a1') , lm)) (S⁻¹ ↓)) ≡
         (E₃raw , inj₂ ((₁₊ a1' , ₀) , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ a1' , - ₁₊ a1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') (- ₁₊ a1') (λ ()))
              (Eq.cong (₁₊ a1' ,_) bf3)))))

    r6 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') ,
           inj₂ ((₀ , b2 + - ₁₊ a1') , lm2))) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₁₊ a1') ,
           inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') ,
          inj₂ ((₀ , b2 + - ₁₊ a1') , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ a1')
          (inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ a1')
            (inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d ,
              inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
            (it-dDS-a0 p-1 (- ₁₊ a1')))))

    r7 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') ,
           inj₂ ((₀ , b2 + - ₁₊ a1') , lm2))) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , cF)
    r7 = Eq.trans
      (ract-↑-≡ (₀ , - ₁₊ a1')
        (inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (b2 + - ₁₊ a1') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , - ₁₊ a1') , c))
          (Eq.trans (ract-S^-coset (₀ , b2 + - ₁₊ a1') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (b2 + - ₁₊ a1'))))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            E₁raw • ((Hdir (₁₊ a1' , ₁₊ a1') ↓ᵏ (₁₊ m)) •
              (E₃raw • (WDe' • (HH • (S ^ p-1 • (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5e)) .proj₁)
          r1)
      (Eq.cong (λ t → E₁raw • t)
      (Eq.cong (λ t → (Hdir (₁₊ a1' , ₁₊ a1') ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5e)) .proj₁)
          r3)
      (Eq.cong (λ t → E₃raw • t)
      (Eq.trans (Eq.cong₂ _•_ Eq.refl
          (Eq.cong₂ _•_
            (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) (e0 ₀))
            (Eq.cong (λ pr → ((ract3 ᵗ) pr (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
              (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
                  inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
                (e0 ₀)))))
      (Eq.cong (λ t → WDe' • t)
      (Eq.cong (λ t → HH • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → S ^ p-1 • t) (Eq.cong proj₁ r7))))))))))

    Rclean : E₁raw • ((Hdir (₁₊ a1' , ₁₊ a1') ↓ᵏ (₁₊ m)) •
               (E₃raw • (WDe' • (HH • (S ^ p-1 • (S ^ p-1) ↑))))) ≈
             S • (WDe' • (HH • (S⁻¹ • S⁻¹ ↑)))
    Rclean =
      trans (trans (cleft
          (ract-S^-resid-a+ (₁₊ a1' , ₀) lm p-1 (λ ()))) left-unit)
      (trans (cleft (unitS {₁₊ m} a1'))
        (cright (trans (cleft
          (ract-S^-resid-a+ (₁₊ a1' , - ₁₊ a1') lm p-1 (λ ())))
          left-unit)))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans id11e
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5e)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5e)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) pr (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
              inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
            (e0 ₀)))
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
