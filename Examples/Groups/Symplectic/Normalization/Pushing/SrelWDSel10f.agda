------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on doubly-inj₂ boxes (₁₊a1',b1)/(₀,₀): the bottom box
-- is dirty, so the CZs escape in bottom-conjugated form WD = H•CZ•H³
-- and the third CZ hits the clause-4 pad, whose S-slots collapse to
-- value 1 under the negation witness.  The residual identity exposes
-- the axiom after an H⁴-cancellation, and the top-wire tail collapses
-- by commutation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
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
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-*)

import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (Sp-1-S ; SinvupS ; H4up)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

  -- The clause-4 pad at width ₂₊ m, S-slots exposed.
  padSA : ∀ (a1' y : Fin (₁₊ p-2)) (B G : ℤ ₚ) →
    (DDCZ.dir-of ((₁₊ a1' , B) ∷ (₁₊ y , G) ∷ []) ↓ᵏ m) ≡
    H • (H ↑ • (CZ • (S^ (- ₁₊ y * ((₁₊ a1' , λ ()) ⁻¹) .proj₁) •
      (H ^ 3 • (S^ (- ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁) ↑ •
        (H ↑) ^ 3)))))
  padSA a1' y B G = Eq.cong₂
    (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
    (S^-↓ᵏ (- ₁₊ y * ((₁₊ a1' , λ ()) ⁻¹) .proj₁) m)
    (Eq.trans (↑↓ᵏ-comm (S^ (- ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁)) m)
      (Eq.cong _↑
        (S^-↓ᵏ (- ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁) m)))

  -- The top-wire tail collapses: H↑ • S⁻¹↑ • H³ • S↑ • H↑³ ≈ H³.
  topcol : H ↑ • (S⁻¹ ↑ • (H {₁₊ m} ^ 3 • (S ↑ • (H ↑) ^ 3))) ≈ H ^ 3
  topcol =
    trans (cright (cright (trans (sym assoc)
      (trans (cleft (comm⇒pow-comm {w = H} {v = S ↑} 3 1
          (lemma-comm-H-w↑ S)))
        assoc))))
    (trans (cright (cright (cright (comm⇒pow-comm {w = H} {v = H ↑} 3 3
        (lemma-comm-H-w↑ H)))))
    (trans (cright (trans (sym assoc) (trans (cleft SinvupS) left-unit)))
    (trans (sym assoc) (trans (cleft H4up) left-unit))))

  -- The residual identity for the (₁₊,·)/(₀,₀) pattern.
  idA00 : WD • (H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))) ≈
          S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • WD))
  idA00 =
    trans assoc
    (trans (cright assoc)
    (trans (cright (cright (trans assoc (trans (cright assoc)
      (trans (cright (cright (sym assoc)))
      (trans (cright (sym assoc))
      (trans (sym assoc)
      (trans (cleft (axiom order-H)) left-unit))))))))
    (trans (cright (trans (cright (sym assoc))
      (trans (sym assoc) (trans (cleft (axiom selinger-c10))
        (cleft (refl' fixdownF))))))
    (trans (cright (trans assoc (trans (cright assoc)
      (trans (cright (cright assoc))
      (trans (cright (cright (cright assoc)))
      (trans (cright (cright (cright (cright assoc))))
        (cright (cright (cright (cright (cright assoc)))))))))))
    (trans (cright (cright (cright (cright (cright (cright (cright
      (trans (sym assoc) (trans (cleft (Sp-1-S {₁₊ m})) left-unit)))))))))
    (trans (cright (cright (cright (cright (cright topcol)))))
    (trans (trans (sym assoc)
      (trans (cleft (lemma-comm-H-w↑ S⁻¹)) assoc))
    (trans (cright (trans (sym assoc)
      (trans (cleft (lemma-comm-H-w↑ H)) assoc)))
           (cright (cright (trans (sym assoc)
      (trans (cleft (lemma-comm-H-w↑ S⁻¹)) assoc))))))))))))
    where
    fixdownF : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownF = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

  c10-go-a00 : ∀ (b1 : ℤ ₚ) (a1' y : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    - ₁₊ a1' ≡ ₁₊ y →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₀) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₀) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-a00 b1 a1' y lm2 eq-y = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , ₀) , lm2)

    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}

    negneg : ∀ (x z : ℤ ₚ) → - x * - z ≡ x * z
    negneg x z = Eq.trans (Eq.sym (-‿distribˡ-* x (- z)))
      (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* x z)))
        (-‿involutive (x * z)))

    yfix : - ₁₊ y ≡ ₁₊ a1'
    yfix = Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a1'))

    zfix0 : ₀ + - ₁₊ a1' ≡ ₁₊ y
    zfix0 = Eq.trans (+-identityˡ (- ₁₊ a1')) eq-y

    zfix : - ₀ + - ₁₊ a1' ≡ ₁₊ y
    zfix = Eq.trans (Eq.cong (_+ - ₁₊ a1') -0#≈0#) zfix0

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    bfix6f : - ₀ + nsum p-1 (- ₁₊ y) ≡ ₁₊ y
    bfix6f = Eq.trans (Eq.cong₂ _+_ -0#≈0#
        (Eq.trans (nsum-p-1 (- ₁₊ y)) (-‿involutive (₁₊ y))))
      (+-identityˡ (₁₊ y))

    vu : - ₁₊ y * ((₁₊ a1' , λ ()) ⁻¹) .proj₁ ≡ ₁
    vu = Eq.trans (Eq.cong (_* ((₁₊ a1' , λ ()) ⁻¹) .proj₁) yfix)
      (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}})

    vv : - ₁₊ a1' * ((₁₊ y , λ ()) ⁻¹) .proj₁ ≡ ₁
    vv = Eq.trans (Eq.cong (- ₁₊ a1' *_)
        (ineg (₁₊ a1' , λ ()) (₁₊ y , λ ()) (Eq.sym eq-y)))
      (Eq.trans (negneg (₁₊ a1') (((₁₊ a1' , λ ()) ⁻¹) .proj₁))
        (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}}))

    PAD1 : Word (Gen (₂₊ m))
    PAD1 = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1 + ₁₊ a1') , inj₂ ((₁₊ y , ₁₊ y) , lm2))

    PADfix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
               inj₂ ((₁₊ y , - ₀) , lm2))) CZ) .proj₁ ≡ PAD1
    PADfix = Eq.trans (padSA a1' y (b1 + - ₀) (- ₀))
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.cong S^ vu)
        (Eq.cong (λ z → S^ z ↑) vv))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            WD • (ε • PAD1)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₀ , v) ↓ᵏ m) ↑) zfix0)
      (Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
          (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
              inj₂ (Hd' (₀ , v) , lm2)))
            zfix0))
        PADfix))

    L-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ (Hd' (₀ , v) , lm2)))
          zfix0))
      (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₁₊ y , u) , lm2)))
        (Eq.cong₂ _+_ (e0 b1) yfix)
        zfix)

    -- RHS letters.
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ y , - ₀) , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
              inj₂ ((₁₊ y , ₁₊ y) , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1f : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) , lm))
    r1f = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 ₀ lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 ₀)))))

    r3f : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₀ , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , - ₀) , lm2)))
    r3f = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₀ , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₀) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (- ₀))))))

    r5f : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₀ , - ₀ + - ₁₊ a1') , lm2))) (H ↑)) ≡
          ((Hdir (₀ , ₁₊ y) ↓ᵏ m) ↑ ,
           inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ ((₁₊ y , - ₀) , lm2)))
    r5f = Eq.cong (λ v → ((Hdir (₀ , v) ↓ᵏ m) ↑ ,
        inj₂ ((₁₊ a1' , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2))))
      zfix

    r6f : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          (E₆raw ↑ , inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2)))
    r6f = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₀) (inj₂ ((₁₊ y , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₀) , c))
          (Eq.trans (ract-S^-coset (₁₊ y , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ y) (- ₀) (λ ()))
                (Eq.cong (₁₊ y ,_) bfix6f))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            (S ^ p-1) ↑ • (H ↑ • ((S ^ p-1) ↑ • (WD •
              ((Hdir (₀ , ₁₊ y) ↓ᵏ m) ↑ • (E₆raw ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1f)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → H ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3f)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → WD • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5f)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ y) ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6f)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2))) u) .proj₁)
          (↓-pow-S p-1)))))))))))

    Rclean : (S ^ p-1) ↑ • (H ↑ • ((S ^ p-1) ↑ • (WD •
               ((Hdir (₀ , ₁₊ y) ↓ᵏ m) ↑ • (E₆raw ↑ • E₇raw))))) ≈
             S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • WD))
    Rclean = cright (cright (cright (trans (cright
        (trans left-unit
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
      (trans (cright left-unit)
      (trans idA00
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1f)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3f)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5f)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6f)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₀)
          (inj₂ ((₁₊ y , ₁₊ y) , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ y , ₁₊ y) , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₀) (λ ())))
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , v) ,
            inj₂ ((₁₊ y , ₁₊ y) , lm2)))
          (Eq.cong₂ _+_ (e0 b1) nfixa1))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
