------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₁₊a1',₁₊b1'')/(₀,b2), branch α:
-- b₁ ≡ -a₁, so both H-escapes are the anti-diagonal unit HH • S⁻¹ and
-- the residual rests on TW3 (H • S⁻¹ • H ≈ S • H • S), which frees the
-- CZ • H • CZ the axiom needs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11f
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

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; comm-Spow-↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (TW3 ; H5 ; SSinv ; Sp-1-S ; unitHS)

------------------------------------------------------------------------
-- The branch-α residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑)

  private
    WDf : Word (Gen (₂₊ m))
    WDf = H • (CZ • H ^ 3)

    SCZf : S • CZ ≈ CZ • S
    SCZf = sym (axiom comm-CZ-S↓)

    SupH3f : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3f = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    fixdown11f : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdown11f = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  id11f : WDf • ((HH • S⁻¹) • WDf) ≈ HH • (S⁻¹ • (CZ • S⁻¹ ↑))
  id11f = begin
    WDf • ((HH • S⁻¹) • WDf)
      ≈⟨ trans assoc (cright assoc) ⟩
    H • (CZ • (H ^ 3 • ((HH • S⁻¹) • WDf)))
      ≈⟨ cright (cright (trans (cright assoc)
           (trans (sym assoc) (cleft H5)))) ⟩
    H • (CZ • (H • (S⁻¹ • (H • (CZ • H ^ 3)))))
      ≈⟨ cright (cright (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft TW3) (trans assoc (cright assoc)))))) ⟩
    H • (CZ • (S • (H • (S • (CZ • H ^ 3)))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft SCZf) assoc))))) ⟩
    H • (CZ • (S • (H • (CZ • (S • H ^ 3)))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym SCZf)) assoc)) ⟩
    H • (S • (CZ • (H • (CZ • (S • H ^ 3)))))
      ≈⟨ cright (cright (trans (cright (sym assoc))
           (trans (sym assoc)
             (cleft (trans (axiom selinger-c11)
               (refl' fixdown11f)))))) ⟩
    H • (S • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))) •
      (S • H ^ 3)))
      ≈⟨ cright (trans (cright assoc)
           (trans (sym assoc)
           (trans (cleft SSinv) left-unit))) ⟩
    H • ((H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))) • (S • H ^ 3))
      ≈⟨ cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright assoc)))))))) ⟩
    H • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • (S⁻¹ ↑ • (S • H ^ 3)))))))
      ≈⟨ cright (cright (cright (cright
           (trans (cright (cright (trans (sym assoc)
             (trans (cleft (sym (comm-Spow-↑ 1 S⁻¹))) assoc))))
           (trans (cright (trans (sym assoc)
             (trans (cleft Sp-1-S) left-unit)))
           (trans (cright SupH3f)
             (trans (sym assoc)
               (trans (cleft (axiom order-H)) left-unit)))))))) ⟩
    H • (H • (S⁻¹ • (CZ • S⁻¹ ↑)))
      ≈⟨ sym assoc ⟩
    HH • (S⁻¹ • (CZ • S⁻¹ ↑)) ∎

------------------------------------------------------------------------
-- The branch-α orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    WDf' : Word (Gen (₂₊ m))
    WDf' = H • (CZ • H ^ 3)

  c11-go-ab0α : ∀ (b2 : ℤ ₚ) (a1' b1'' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ₁₊ b1'' + ₁₊ a1' ≡ ₀ →
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-ab0α b2 a1' b1'' lm2 eqY = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    veq : ₁₊ b1'' ≡ - ₁₊ a1'
    veq = Eq.trans (Eq.sym (+-identityʳ (₁₊ b1'')))
      (Eq.trans (Eq.cong (₁₊ b1'' +_) (Eq.sym (+-inverseʳ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc (₁₊ b1'') (₁₊ a1') (- ₁₊ a1')))
      (Eq.trans (Eq.cong (_+ - ₁₊ a1') eqY)
        (+-identityˡ (- ₁₊ a1')))))

    negB : - ₁₊ b1'' ≡ ₁₊ a1'
    negB = Eq.trans (Eq.cong -_ veq) (-‿involutive (₁₊ a1'))

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixb1 : nsum p-1 (- ₁₊ b1'') ≡ ₁₊ b1''
    nfixb1 = Eq.trans (nsum-p-1 (- ₁₊ b1'')) (-‿involutive (₁₊ b1''))

    bR1 : ₁₊ b1'' + nsum p-1 (- ₁₊ a1') ≡ ₀
    bR1 = Eq.trans (Eq.cong (₁₊ b1'' +_) nfixa1) eqY

    bR6 : - ₀ + nsum p-1 (- ₁₊ b1'') ≡ - ₁₊ a1'
    bR6 = Eq.trans (Eq.cong₂ _+_ -0#≈0# nfixb1)
      (Eq.trans (+-identityˡ (₁₊ b1'')) veq)

    r5cast : - ₁₊ a1' + - ₀ ≡ ₁₊ b1''
    r5cast = Eq.trans (e0 (- ₁₊ a1')) (Eq.sym veq)

    hdfix5 : Hd' (₀ , ₁₊ b1'') ≡ (₁₊ b1'' , - ₀)
    hdfix5 = Eq.refl

    cL2 : (b2 + - ₁₊ a1') + - ₁₊ b1'' ≡ b2
    cL2 = Eq.trans (Eq.cong ((b2 + - ₁₊ a1') +_) negB)
      (Eq.trans (+-assoc b2 (- ₁₊ a1') (₁₊ a1'))
      (Eq.trans (Eq.cong (b2 +_) (+-inverseˡ (₁₊ a1')))
        (+-identityʳ b2)))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ b1'' , - ₁₊ a1') , inj₂ ((₀ , b2) , lm2))

    -- LHS.
    L-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡
            WDf' • ((Hdir (₁₊ a1' , ₁₊ b1'') ↓ᵏ (₁₊ m)) • WDf')
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) (e0 (₁₊ b1'')))
      (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 (₁₊ b1'')))))

    L-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 (₁₊ b1''))))
      (Eq.cong₂ (λ v w → inj₂ ((₁₊ b1'' , v) , inj₂ ((₀ , w) , lm2)))
        (e0 (- ₁₊ a1')) cL2)

    -- RHS.
    E₁raw = ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₀) , lm)) (S ^ p-1)) .proj₁

    REST5f = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    r1 : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (S⁻¹ ↓)) ≡
         (E₁raw , inj₂ ((₁₊ a1' , ₀) , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , ₁₊ b1'') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') (₁₊ b1'') (λ ()))
              (Eq.cong (₁₊ a1' ,_) bR1)))))

    r3 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₁₊ a1') , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₁₊ a1') lm p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (it-dDS-a0 p-1 (- ₁₊ a1')))))

    r5 : ((ract3 ᵗ) (inj₂ ((₀ , - ₁₊ a1' + - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2))) (H ↓)) ≡
         (ε , inj₂ ((₁₊ b1'' , - ₀) , lm))
    r5 = Eq.trans
      (Eq.cong₂ (λ v w → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
          inj₂ (Hd' (₀ , v) , inj₂ ((₀ , w) , lm2))))
        r5cast (e0 b2))
      (Eq.cong (λ d → (ε , inj₂ (d , lm))) hdfix5)

    r6 : ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₀) , lm)) (S⁻¹ ↓)) ≡
         (E₆raw , inj₂ ((₁₊ b1'' , - ₁₊ a1') , lm))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₀) , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ b1'' , - ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ b1'') (- ₀) (λ ()))
              (Eq.cong (₁₊ b1'' ,_) bR6)))))

    r7 : ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₁₊ a1') , lm)) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , cF)
    r7 = Eq.trans
      (ract-↑-≡ (₁₊ b1'' , - ₁₊ a1') lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 b2 lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ b1'' , - ₁₊ a1') , c))
          (Eq.trans (ract-S^-coset (₀ , b2) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 b2)))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            E₁raw • (HH • (S ^ p-1 • (CZ •
              (ε • (E₆raw • (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5f)) .proj₁)
          r1)
      (Eq.cong (λ t → E₁raw • t)
      (Eq.cong (λ t → HH • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5f)) .proj₁)
          r3)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → CZ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          r5)
      (Eq.cong (λ t → ε • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → E₆raw • t) (Eq.cong proj₁ r7))))))))))

    Rclean : E₁raw • (HH • (S ^ p-1 • (CZ •
               (ε • (E₆raw • (S ^ p-1) ↑))))) ≈
             HH • (S⁻¹ • (CZ • S⁻¹ ↑))
    Rclean =
      trans (trans (cleft
          (ract-S^-resid-a+ (₁₊ a1' , ₁₊ b1'') lm p-1 (λ ()))) left-unit)
        (cright (cright (cright (trans left-unit
          (trans (cleft
            (ract-S^-resid-a+ (₁₊ b1'' , - ₀) lm p-1 (λ ())))
            left-unit)))))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (cright (cleft (unitHS {₁₊ m} a1' b1'' veq)))
      (trans id11f
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5f)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5f)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          r5)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

