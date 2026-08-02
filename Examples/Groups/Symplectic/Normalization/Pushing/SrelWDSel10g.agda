------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on doubly-inj₂ boxes (₁₊a1',b1)/(₀,₁₊b2'), branch α:
-- the middle slot b₂ - a₁ vanishes, so b₂ ≡ a₁ and the clause-4 pad's
-- S-slots take the value -1, giving S⁻¹-forms; both sides then meet at
-- a common word after commuting the disjoint-wire letters.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10g
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
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix ; Sp-1-S ; SupCZ ; H5lift)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime using (SdownW)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid

  private
    ract2 = ract {₂₊ m}

    WD : Word (Gen (₂₊ m))
    WD = H • (CZ • H ^ 3)

    PAD4 : Word (Gen (₂₊ m))
    PAD4 = H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ • (H ↑) ^ 3)))))

    LCOM : Word (Gen (₂₊ m))
    LCOM = S⁻¹ ↑ • (H ↑ • (H • (CZ •
      (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (S⁻¹ • H ^ 3)))))))

    fixdownG : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownG = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

  Lα : WD • (H ↑ • WD) ≈ LCOM
  Lα = begin
    WD • (H ↑ • WD)
      ≈⟨ assoc ⟩
    H • ((CZ • H ^ 3) • (H ↑ • (H • (CZ • H ^ 3))))
      ≈⟨ cright assoc ⟩
    H • (CZ • (H ^ 3 • (H ↑ • (H • (CZ • H ^ 3)))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (comm⇒pow-comm {w = H} {v = H ↑} 3 1
               (lemma-comm-H-w↑ H)))
             assoc))) ⟩
    H • (CZ • (H ↑ • (H ^ 3 • (H • (CZ • H ^ 3)))))
      ≈⟨ cright (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (axiom order-H)) left-unit)))))))) ⟩
    H • (CZ • (H ↑ • (CZ • H ^ 3)))
      ≈⟨ cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownG))))) ⟩
    H • ((S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))) •
      H ^ 3)
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))) ⟩
    H • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • H ^ 3)))))))
      ≈⟨ trans (sym assoc) (trans (cleft (lemma-comm-H-w↑ S⁻¹)) assoc) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • H ^ 3)))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ H)) assoc)) ⟩
    S⁻¹ ↑ • (H ↑ • (H • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • H ^ 3)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft SupCZ) assoc)))) ⟩
    LCOM ∎

  Rα : S⁻¹ ↑ • (PAD4 • ((H ↑ • H ↑) • S⁻¹ ↑)) ≈ LCOM
  Rα = begin
    S⁻¹ ↑ • (PAD4 • ((H ↑ • H ↑) • S⁻¹ ↑))
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc)))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ •
      ((H ↑) ^ 3 • ((H ↑ • H ↑) • S⁻¹ ↑))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft H5lift)))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S⁻¹ • (H ^ 3 • (S⁻¹ ↑ •
      (H ↑ • S⁻¹ ↑)))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (comm⇒pow-comm
               {w = H} {v = S⁻¹ ↑} 3 1 (lemma-comm-H-w↑ S⁻¹)))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (comm⇒pow-comm {w = H} {v = H ↑} 3 1
                 (lemma-comm-H-w↑ H)))
             (trans assoc (cright (comm⇒pow-comm
                 {w = H} {v = S⁻¹ ↑} 3 1 (lemma-comm-H-w↑ S⁻¹)))))))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S⁻¹ • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ •
      H ^ 3)))))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft (SdownW S⁻¹))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SdownW H))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (SdownW S⁻¹)) assoc))))))))))))) ⟩
    S⁻¹ ↑ • (H • (H ↑ • (CZ • (S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • H ^ 3)))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ H)) assoc)) ⟩
    LCOM ∎

  idα : WD • (H ↑ • WD) ≈ S⁻¹ ↑ • (PAD4 • ((H ↑ • H ↑) • S⁻¹ ↑))
  idα = trans Lα (sym Rα)

  c10-go-a0bα : ∀ (b1 : ℤ ₚ) (a1' b2' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ₁₊ b2' + - ₁₊ a1' ≡ ₀ →
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-a0bα b1 a1' b2' lm2 eq-X = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , ₁₊ b2') , lm2)

    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}

    beq : ₁₊ b2' ≡ ₁₊ a1'
    beq = Eq.trans (Eq.sym (+-identityʳ (₁₊ b2')))
      (Eq.trans (Eq.cong (₁₊ b2' +_) (Eq.sym (+-inverseˡ (₁₊ a1'))))
      (Eq.trans (Eq.sym (+-assoc (₁₊ b2') (- ₁₊ a1') (₁₊ a1')))
      (Eq.trans (Eq.cong (_+ ₁₊ a1') eq-X)
        (+-identityˡ (₁₊ a1')))))

    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    bfix3g : - ₀ + nsum p-1 (- ₁₊ b2') ≡ ₁₊ b2'
    bfix3g = Eq.trans (Eq.cong₂ _+_ -0#≈0#
        (Eq.trans (nsum-p-1 (- ₁₊ b2')) (-‿involutive (₁₊ b2'))))
      (+-identityˡ (₁₊ b2'))

    vα : - ₁₊ b2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁ ≡ - ₁
    vα = Eq.trans (Eq.cong (λ t → - t * ((₁₊ a1' , λ ()) ⁻¹) .proj₁) beq)
      (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a1')
          (((₁₊ a1' , λ ()) ⁻¹) .proj₁)))
        (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}})))

    vβ : - ₁₊ a1' * ((₁₊ b2' , λ ()) ⁻¹) .proj₁ ≡ - ₁
    vβ = Eq.trans (Eq.cong (- ₁₊ a1' *_)
        (inv-cong (₁₊ b2' , λ ()) (₁₊ a1' , λ ()) beq))
      (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ a1')
          (((₁₊ a1' , λ ()) ⁻¹) .proj₁)))
        (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}})))

    r7fix : (b1 + - ₁₊ b2') + nsum p-1 (- ₁₊ a1') ≡ b1
    r7fix = Eq.trans (Eq.cong₂ _+_
        (Eq.cong (b1 +_) (Eq.cong -_ beq)) nfixa1)
      (Eq.trans (+-assoc b1 (- ₁₊ a1') (₁₊ a1'))
      (Eq.trans (Eq.cong (b1 +_) (+-inverseˡ (₁₊ a1')))
        (+-identityʳ b1)))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , - ₁₊ a1') , lm2))

    L-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
              .proj₁ ≡
            WD • (H ↑ • WD)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₀ , v) ↓ᵏ m) ↑) eq-X)
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ (Hd' (₀ , v) , lm2)))
          eq-X)))

    L-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • H ↑ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₁₊ a1' , b1 + - ₀) ,
            inj₂ (Hd' (₀ , v) , lm2)))
          eq-X))
      (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₀ , u) , lm2)))
        (Eq.trans (Eq.cong (_+ - ₀) (e0 b1)) (e0 b1))
        (Eq.trans (Eq.cong (_+ - ₁₊ a1') -0#≈0#)
          (+-identityˡ (- ₁₊ a1'))))

    -- RHS letters.
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹) .proj₁
    E₇raw = ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
              inj₂ ((₀ , - ₁₊ b2') , lm2))) (S ^ p-1)) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1g : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1) , lm))
    r1g = Eq.trans (ract-↑-≡ (₁₊ a1' , b1) lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (₁₊ b2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (₁₊ b2'))))))

    r3g : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ b2' , - ₀) , lm2))) (S⁻¹ ↑)) ≡
          (E₃raw ↑ , inj₂ ((₁₊ a1' , b1) ,
            inj₂ ((₁₊ b2' , ₁₊ b2') , lm2)))
    r3g = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ b2' , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ b2') (- ₀) (λ ()))
                (Eq.cong (₁₊ b2' ,_) bfix3g))))))

    PADfixα : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) ,
                inj₂ ((₁₊ b2' , ₁₊ b2') , lm2))) CZ) .proj₁ ≡ PAD4
    PADfixα = Eq.trans (padSA a1' b2' b1 (₁₊ b2'))
      (Eq.cong₂
        (λ s t → H • (H ↑ • (CZ • (s • (H ^ 3 • (t • (H ↑) ^ 3))))))
        (Eq.trans (Eq.cong S^ vα) SIfix)
        (Eq.cong _↑ (Eq.trans (Eq.cong S^ vβ) SIfix)))

    r5g : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₁₊ b2' , ₁₊ b2' + - ₁₊ a1') , lm2))) (H ↑)) ≡
          ((H ↑ • H ↑) ,
           inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
             inj₂ ((₀ , - ₁₊ b2') , lm2)))
    r5g = Eq.cong (λ v → ((Hdir (₁₊ b2' , v) ↓ᵏ m) ↑ ,
        inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') , inj₂ (Hd' (₁₊ b2' , v) , lm2))))
      eq-X

    r6g : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₀ , - ₁₊ b2') , lm2))) (S⁻¹ ↑)) ≡
          ((S ^ p-1) ↑ , inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₀ , - ₁₊ b2') , lm2)))
    r6g = Eq.trans
      (ract-↑-≡ (₁₊ a1' , b1 + - ₁₊ b2') (inj₂ ((₀ , - ₁₊ b2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₁₊ b2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') , c))
          (Eq.trans (ract-S^-coset (₀ , - ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (- ₁₊ b2'))))))

    R-fix : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
              (E₃raw ↑ • (PAD4 • ((H ↑ • H ↑) •
                ((S ^ p-1) ↑ • E₇raw)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1g)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3g)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.trans (Eq.cong₂ _•_ PADfixα Eq.refl)
      (Eq.cong (λ t → PAD4 • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5g)
      (Eq.cong (λ t → (H ↑ • H ↑) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6g)
      (Eq.cong ((S ^ p-1) ↑ •_)
        (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₀ , - ₁₊ b2') , lm2))) u) .proj₁)
          (↓-pow-S p-1))))))))))))

    Rclean : (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
               (E₃raw ↑ • (PAD4 • ((H ↑ • H ↑) •
                 ((S ^ p-1) ↑ • E₇raw))))) ≈
             S⁻¹ ↑ • (PAD4 • ((H ↑ • H ↑) • S⁻¹ ↑))
    Rclean =
      trans (cright left-unit)
      (trans (cright (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ b2' , - ₀) lm2 p-1 (λ ())))) left-unit))
             (cright (cright (cright (trans (cright
          (ract-S^-resid-a+ (₁₊ a1' , b1 + - ₁₊ b2')
            (inj₂ ((₀ , - ₁₊ b2') , lm2)) p-1 (λ ())))
        right-unit)))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans idα
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1g)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3g)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5g)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6g)
      (Eq.trans (Eq.cong (λ u → ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1 + - ₁₊ b2') ,
            inj₂ ((₀ , - ₁₊ b2') , lm2))) u) .proj₂)
          (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₁₊ a1' , b1 + - ₁₊ b2')
          (inj₂ ((₀ , - ₁₊ b2') , lm2)) p-1)
      (Eq.trans (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , - ₁₊ b2') , lm2)))
          (it-dDS-nz p-1 (₁₊ a1') (b1 + - ₁₊ b2') (λ ())))
        (Eq.cong₂ (λ v u → inj₂ ((₁₊ a1' , v) , inj₂ ((₀ , u) , lm2)))
          r7fix
          (Eq.cong -_ beq))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
                (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)
