------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 cases of srel-wd on doubly-inj₂ cosets.  c11 is the
-- ↓/↑ mirror of c10: the H and the first three S⁻¹ act on the BOTTOM
-- box through the width-native engines (no lifting), and only the
-- final S⁻¹↑ touches the upper box.  This module does the all-zero
-- pattern, where every escape is the letter itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11
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
  using (-0#≈0# ; -‿involutive)

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; H↑3H↑≈ε)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (TW ; unitS ; Sp-1-S ; SinvupS)
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

  -- Both boxes clean: every CZ escapes as CZ, every bottom H as H and
  -- every S⁻¹ as S^(p-1), so the residual is the axiom itself.
  c11-go-000 : ∀ (b2 : ℤ ₚ) (lm2 : C (₁₊ m)) →
    ((ract2 ᵗ) (inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-000 b2 lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    z00 : - ₀ + - ₀ ≡ ₀
    z00 = Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) (+-identityʳ ₀)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    cF : C (₃₊ m)
    cF = inj₂ ((₀ , ₀) , inj₂ ((₀ , b2) , lm2))

    -- LHS: the middle H is the bottom H on the (₀,₀) box.
    L-fix : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₁ ≡
            CZ • (H • CZ)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₀ , v) ↓ᵏ (₁₊ m)) (e0 ₀))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong₂ (λ v w → inj₂ ((v , - ₀) , inj₂ ((₀ , w) , lm2)))
          (e0 ₀) (e0 b2))))

    L-c : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong₂ (λ v w → inj₂ ((v , - ₀) , inj₂ ((₀ , w) , lm2)))
          (e0 ₀) (e0 b2)))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        z00 (e0 b2))

    REST5 = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    -- RHS: r1/r3/r6 are the a=0 S-engine, r2/r5 the bottom H, r4 the
    -- clean CZ and r7 the lifted S-power.
    r1 : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , ₀) , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 ₀ lm p-1)
        (Eq.trans (ract-S^-coset (₀ , ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 ₀))))

    r3 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₀) , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , - ₀) , lm)) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₀) lm p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (- ₀)))))

    r6 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2))) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , - ₀) , inj₂ ((₀ , b2 + - ₀) , lm2)))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
          inj₂ ((₀ , b2 + - ₀) , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (- ₀) (inj₂ ((₀ , b2 + - ₀) , lm2)) p-1)
        (Eq.trans (ract-S^-coset (₀ , - ₀)
            (inj₂ ((₀ , b2 + - ₀) , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , b2 + - ₀) , lm2)))
            (it-dDS-a0 p-1 (- ₀)))))

    r7 : ((ract2 ᵗ) (inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2))) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , inj₂ ((₀ , - ₀) ,
           inj₂ ((₀ , b2 + - ₀) , lm2)))
    r7 = Eq.trans
      (ract-↑-≡ (₀ , - ₀) (inj₂ ((₀ , b2 + - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (b2 + - ₀) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , - ₀) , c))
          (Eq.trans (ract-S^-coset (₀ , b2 + - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (b2 + - ₀))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            S ^ p-1 • (H • (S ^ p-1 • (CZ • (H • (S ^ p-1 •
              (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5)) .proj₁)
          r1)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → CZ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
              inj₂ (Hd' (₀ , v) , inj₂ ((₀ , b2 + - ₀) , lm2)))) z00))
      (Eq.cong (λ t → (Hdir (₀ , ₀) ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → S ^ p-1 • t) (Eq.cong proj₁ r7))))))))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (axiom selinger-c11)
      (sym (refl' R-fix)))

    R-c : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          (Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ (₁₊ m)) ,
              inj₂ (Hd' (₀ , v) , inj₂ ((₀ , b2 + - ₀) , lm2)))) z00))
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
      (Eq.trans (Eq.cong proj₂ r7)
        (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
          -0#≈0# (e0 b2))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm)) (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , ₀) , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

------------------------------------------------------------------------
-- The (₀,₁₊b1')/(₀,b2) pattern: the middle H escapes ε and rotates
-- b₁ into the a-slot, so the last CZ escapes bottom-conjugated.  The
-- residual identity is c10's residkey mirrored, and it rests on the
-- same one-wire fact TW — here applied on the bottom wire directly.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑)

  private
    ract2' = ract {₂₊ m}

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    SdownCZ : S⁻¹ • CZ ≈ CZ • S⁻¹
    SdownCZ = comm⇒pow-comm {w = S} {v = CZ} p-1 1
      (sym (axiom comm-CZ-S↓))

    SupH3 : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3 = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    fixdown11 : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdown11 = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  -- The mirror of residkey: the bottom S⁻¹ crosses the CZ and the
  -- remaining S⁻¹•H•S⁻¹•H³ is TW.
  residkey11 : CZ • WD ≈ S⁻¹ • (WD • (S • S⁻¹ ↑))
  residkey11 =
    trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft (axiom selinger-c11))
    (trans (cleft (refl' fixdown11))
    (trans assoc (cright inner)))))
    where
    inner : (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))) • H ^ 3 ≈
            WD • (S • S⁻¹ ↑)
    inner =
      trans assoc
      (trans (cright assoc)
      (trans (cright (cright assoc))
      (trans (cright (cright (cright assoc)))
      (trans (cright (cright (cright (cright assoc))))
      (trans (cright (cright (cright (cright (cright SupH3)))))
      (trans (cright (trans (sym assoc)
        (trans (cleft SdownCZ) assoc)))
      (trans (cright (cright (trans
          (trans (cright (cright (sym assoc)))
          (trans (cright (sym assoc)) (sym assoc)))
          (trans (cleft (TW {₁₊ m})) assoc))))
        (trans (cright (sym assoc)) (sym assoc)))))))))


  c11-go-0b1 : ∀ (b1' : Fin (₁₊ p-2)) (b2 : ℤ ₚ) (lm2 : C (₁₊ m)) →
    ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-0b1 b1' b2 lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    z00 : - ₀ + - ₀ ≡ ₀
    z00 = Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) (+-identityʳ ₀)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    nfixb : nsum p-1 (- ₁₊ b1') ≡ ₁₊ b1'
    nfixb = Eq.trans (nsum-p-1 (- ₁₊ b1')) (-‿involutive (₁₊ b1'))

    bfix3 : - ₀ + nsum p-1 (- ₁₊ b1') ≡ ₁₊ b1'
    bfix3 = Eq.trans (Eq.cong₂ _+_ -0#≈0# nfixb) (+-identityˡ (₁₊ b1'))

    bfix6 : - ₁₊ b1' + nsum p-1 (- ₁₊ b1') ≡ ₀
    bfix6 = Eq.trans (Eq.cong (- ₁₊ b1' +_) nfixb) (+-inverseˡ (₁₊ b1'))

    hdfix : Hd' (₀ , ₁₊ b1') ≡ (₁₊ b1' , - ₀)
    hdfix = Eq.refl

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ b1' , ₀) , inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))

    L-fix : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡ CZ • (ε • WD)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir (₀ , v) ↓ᵏ (₁₊ m)) (e0 (₁₊ b1')))
      (Eq.cong (λ pr → ((ract2' ᵗ) pr CZ) .proj₁)
        (Eq.trans
          (Eq.cong₂ (λ v w → inj₂ (Hd' (₀ , v) , inj₂ ((₀ , w) , lm2)))
            (e0 (₁₊ b1')) (e0 b2))
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , b2) , lm2))) hdfix))))

    L-c : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2' ᵗ) pr CZ) .proj₂)
        (Eq.trans
          (Eq.cong₂ (λ v w → inj₂ (Hd' (₀ , v) , inj₂ ((₀ , w) , lm2)))
            (e0 (₁₊ b1')) (e0 b2))
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , b2) , lm2))) hdfix)))
      (Eq.cong (λ v → inj₂ ((₁₊ b1' , v) ,
          inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) z00)

    REST5' = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    E₃raw = ((ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₁₊ b1') ,
              inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) (S ^ p-1)) .proj₁

    q1 : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) (S⁻¹ ↓)) ≡
         (S ^ p-1 , inj₂ ((₀ , ₁₊ b1') , lm))
    q1 = Eq.trans
      (Eq.cong (λ w → (ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_
        (ract-S^-resid-a0 (₁₊ b1') lm p-1)
        (Eq.trans (ract-S^-coset (₀ , ₁₊ b1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm)) (it-dDS-a0 p-1 (₁₊ b1')))))

    q3 : ((ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) (S⁻¹ ↓)) ≡
         (E₃raw , inj₂ ((₁₊ b1' , ₁₊ b1') , lm))
    q3 = Eq.trans
      (Eq.cong (λ w → (ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₀) , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ b1' , - ₀) lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ b1') (- ₀) (λ ()))
              (Eq.cong (₁₊ b1' ,_) bfix3)))))

    q5 : ((ract2' ᵗ) (inj₂ ((₁₊ b1' , ₁₊ b1' + - ₀) ,
           inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) (H ↓)) ≡
         ((Hdir (₁₊ b1' , ₁₊ b1') ↓ᵏ (₁₊ m)) ,
          inj₂ ((₁₊ b1' , - ₁₊ b1') ,
            inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)))
    q5 = Eq.cong (λ v → ((Hdir (₁₊ b1' , v) ↓ᵏ (₁₊ m)) ,
        inj₂ (Hd' (₁₊ b1' , v) , inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))))
      (e0 (₁₊ b1'))

    q6 : ((ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₁₊ b1') ,
           inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↓)) ≡
         (E₆raw , inj₂ ((₁₊ b1' , ₀) ,
           inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)))
    q6 = Eq.trans
      (Eq.cong (λ w → (ract2' ᵗ) (inj₂ ((₁₊ b1' , - ₁₊ b1') ,
          inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) w) (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ b1' , - ₁₊ b1')
            (inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)) p-1)
          (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)))
            (Eq.trans (it-dDS-nz p-1 (₁₊ b1') (- ₁₊ b1') (λ ()))
              (Eq.cong (₁₊ b1' ,_) bfix6)))))

    q7 : ((ract2' ᵗ) (inj₂ ((₁₊ b1' , ₀) ,
           inj₂ ((₀ , b2 + - ₁₊ b1') , lm2))) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , cF)
    q7 = Eq.trans
      (ract-↑-≡ (₁₊ b1' , ₀) (inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (b2 + - ₁₊ b1') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ b1' , ₀) , c))
          (Eq.trans (ract-S^-coset (₀ , b2 + - ₁₊ b1') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (b2 + - ₁₊ b1'))))))

    R-fix : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            S ^ p-1 • (ε • (E₃raw • (WD •
              ((Hdir (₁₊ b1' , ₁₊ b1') ↓ᵏ (₁₊ m)) •
                (E₆raw • (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2' ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5')) .proj₁)
          q1)
      (Eq.cong (λ t → S ^ p-1 • t)
      (Eq.cong (λ t → ε • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2' ᵗ) (pr .proj₂) (CZ • REST5')) .proj₁)
          q3)
      (Eq.cong (λ t → E₃raw • t)
      (Eq.cong (λ t → WD • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2' ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
          q5)
      (Eq.cong (λ t → (Hdir (₁₊ b1' , ₁₊ b1') ↓ᵏ (₁₊ m)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2' ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          q6)
        (Eq.cong (λ t → E₆raw • t) (Eq.cong proj₁ q7))))))))))

    Rclean : S ^ p-1 • (ε • (E₃raw • (WD •
               ((Hdir (₁₊ b1' , ₁₊ b1') ↓ᵏ (₁₊ m)) •
                 (E₆raw • (S ^ p-1) ↑))))) ≈
             S⁻¹ • (WD • (S • S⁻¹ ↑))
    Rclean =
      cright (trans left-unit
        (trans (cleft (ract-S^-resid-a+ (₁₊ b1' , - ₀) lm p-1 (λ ())))
        (trans left-unit
          (cright (trans (cleft (unitS {₁₊ m} b1'))
            (cright (trans (cleft
                (ract-S^-resid-a+ (₁₊ b1' , - ₁₊ b1')
                  (inj₂ ((₀ , b2 + - ₁₊ b1') , lm2)) p-1 (λ ())))
              left-unit)))))))

    resid≈ : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (cright left-unit)
      (trans residkey11
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2' ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5')) .proj₂)
          q1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2' ᵗ) (pr .proj₂) (CZ • REST5')) .proj₂)
          q3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2' ᵗ) (pr .proj₂) (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          q5)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2' ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          q6)
        (Eq.cong proj₂ q7))))

    coset≡ : ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract2' ᵗ) (inj₂ ((₀ , ₁₊ b1') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)


------------------------------------------------------------------------
-- The (₀,₀)/(₁₊a2',b2) pattern.  The first CZ escapes top-conjugated
-- (W), the middle H escapes ε, and the last CZ hits the clause-4 pad
-- whose two slots BOTH take the value 1 (because the rotated box is
-- exactly -a₂).  The identity then closes with four cancellations.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)

  private
    W2 : Word (Gen (₂₊ m))
    W2 = H ↑ • (CZ • (H ↑) ^ 3)

    PAD1c : Word (Gen (₂₊ m))
    PAD1c = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    HWa : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HWa w = lemma-comm-H-w↑ w

    SinvHup : S⁻¹ • H ↑ ≈ H ↑ • S⁻¹
    SinvHup = comm⇒pow-comm {w = S} {v = H ↑} p-1 1
      (lemma-comm-S-w↑ H)

    SupH3a : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3a = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    fixdown11a : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdown11a = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

  idc11a : W2 • PAD1c ≈ S⁻¹ • (H • (S⁻¹ • W2))
  idc11a = begin
    W2 • PAD1c
      ≈⟨ trans assoc (cright assoc) ⟩
    H ↑ • (CZ • ((H ↑) ^ 3 • PAD1c))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (sym (HWa (H ^ 3))))
           (trans assoc
           (trans (cright (sym assoc))
           (trans (cright (cleft H↑3H↑≈ε)) (cright left-unit))))))) ⟩
    H ↑ • (CZ • (H • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (trans (cright (sym assoc)) (sym assoc)) ⟩
    H ↑ • ((CZ • (H • CZ)) • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))
      ≈⟨ cright (cleft (trans (axiom selinger-c11) (refl' fixdown11a))) ⟩
    H ↑ • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))) •
      (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))
      ≈⟨ cright (trans assoc (cright (trans assoc (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright assoc)))))))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (lemma-comm-S-w↑ S⁻¹))) assoc)))))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S • (S⁻¹ ↑ • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (Sp-1-S {₁₊ m})) left-unit)))))))  ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H •
      (S⁻¹ ↑ • (H ^ 3 • (S ↑ • (H ↑) ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft SupH3a) assoc))))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H •
      (H ^ 3 • (S⁻¹ ↑ • (S ↑ • (H ↑) ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (axiom order-H)) left-unit)))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ •
      (S⁻¹ ↑ • (S ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft SinvupS) left-unit)))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H ↑) ^ 3))))
      ≈⟨ trans (sym assoc) (trans (cleft (sym SinvHup)) assoc) ⟩
    S⁻¹ • (H ↑ • (H • (S⁻¹ • (CZ • (H ↑) ^ 3))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (HWa H))) assoc)) ⟩
    S⁻¹ • (H • (H ↑ • (S⁻¹ • (CZ • (H ↑) ^ 3))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (sym SinvHup)) assoc))) ⟩
    S⁻¹ • (H • (S⁻¹ • (H ↑ • (CZ • (H ↑) ^ 3)))) ∎

