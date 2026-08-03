------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case βα: Y = b₂ - a₁ ≡ y
-- is nonzero but Z = b₂ + a₂ vanishes, so y ≡ -(a₂ + a₁).  All three
-- L-side groups (general pad, a₂/y unit, a₁/y pad) annihilate through
-- the telescopes qŷ·rŷ ≡ 1, v₁ - rŷ ≡ 1, u₁ + uy ≡ 1, -irŷ + vy ≡ 1,
-- leaving exactly HH↑ • S⁻¹↑ • WD.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10l
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
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ;
         -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (iexp ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix ; Sp-1-S ; SupSinv ; SinvupS ; H4up)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime

------------------------------------------------------------------------
-- The value kit under ySum : y ≡ -(a₂ + a₁).

module BAValues (a1' a2' y : Fin (₁₊ p-2))
  (ySum : ₁₊ y ≡ - (₁₊ a2' + ₁₊ a1')) where

  A₁* A₂* Y* : ℤ* ₚ
  A₁* = (₁₊ a1' , λ ())
  A₂* = (₁₊ a2' , λ ())
  Y*  = (₁₊ y , λ ())

  iA₁ iA₂ iY : ℤ ₚ
  iA₁ = (A₁* ⁻¹) .proj₁
  iA₂ = (A₂* ⁻¹) .proj₁
  iY  = (Y* ⁻¹) .proj₁

  qŷp rŷp : ℤ* ₚ
  qŷp = A₂* *' (Y* ⁻¹)
  rŷp = Y* *' (A₂* ⁻¹)

  u₁v v₁v uyv vyv rŷv qŷv irŷ : ℤ ₚ
  u₁v = - ₁₊ a2' * iA₁
  v₁v = - ₁₊ a1' * iA₂
  uyv = - ₁₊ y * iA₁
  vyv = - ₁₊ a1' * iY
  rŷv = ₁₊ y * iA₂
  qŷv = ₁₊ a2' * iY
  irŷ = (rŷp ⁻¹) .proj₁

  private
    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instA₂ = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instY  = nztoℕ {y = ₁₊ y} {neq0 = λ ()}
    instRŷ = nztoℕ {y = rŷp .proj₁} {neq0 = rŷp .proj₂}
    instQŷ = nztoℕ {y = qŷp .proj₁} {neq0 = qŷp .proj₂}

  open Eq.≡-Reasoning

  negneg : ∀ (s t : ℤ ₚ) → - s * - t ≡ s * t
  negneg s t = Eq.trans (Eq.sym (-‿distribˡ-* s (- t)))
    (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* s t)))
      (-‿involutive (s * t)))

  wYA : ₁₊ a1' + ₁₊ y ≡ - ₁₊ a2'
  wYA = begin
    ₁₊ a1' + ₁₊ y
      ≡⟨ Eq.cong (₁₊ a1' +_) ySum ⟩
    ₁₊ a1' + - (₁₊ a2' + ₁₊ a1')
      ≡⟨ Eq.cong (₁₊ a1' +_) (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ a1'))) ⟩
    ₁₊ a1' + (- ₁₊ a2' + - ₁₊ a1')
      ≡⟨ Eq.cong (₁₊ a1' +_) (+-comm (- ₁₊ a2') (- ₁₊ a1')) ⟩
    ₁₊ a1' + (- ₁₊ a1' + - ₁₊ a2')
      ≡⟨ Eq.sym (+-assoc (₁₊ a1') (- ₁₊ a1') (- ₁₊ a2')) ⟩
    (₁₊ a1' + - ₁₊ a1') + - ₁₊ a2'
      ≡⟨ Eq.cong (_+ - ₁₊ a2') (+-inverseʳ (₁₊ a1')) ⟩
    ₀ + - ₁₊ a2'
      ≡⟨ +-identityˡ (- ₁₊ a2') ⟩
    - ₁₊ a2' ∎

  wYB : ₁₊ a2' + ₁₊ y ≡ - ₁₊ a1'
  wYB = begin
    ₁₊ a2' + ₁₊ y
      ≡⟨ Eq.cong (₁₊ a2' +_) ySum ⟩
    ₁₊ a2' + - (₁₊ a2' + ₁₊ a1')
      ≡⟨ Eq.cong (₁₊ a2' +_) (Eq.sym (-‿+-comm (₁₊ a2') (₁₊ a1'))) ⟩
    ₁₊ a2' + (- ₁₊ a2' + - ₁₊ a1')
      ≡⟨ Eq.sym (+-assoc (₁₊ a2') (- ₁₊ a2') (- ₁₊ a1')) ⟩
    (₁₊ a2' + - ₁₊ a2') + - ₁₊ a1'
      ≡⟨ Eq.cong (_+ - ₁₊ a1') (+-inverseʳ (₁₊ a2')) ⟩
    ₀ + - ₁₊ a1'
      ≡⟨ +-identityˡ (- ₁₊ a1') ⟩
    - ₁₊ a1' ∎

  wb1 : v₁v * (((qŷp ⁻¹) ⁻¹) .proj₁ * ((qŷp ⁻¹) ⁻¹) .proj₁) ≡
        v₁v * (qŷv * qŷv)
  wb1 = Eq.cong (v₁v *_)
    (Eq.cong₂ _*_ (inv-involutive qŷp) (inv-involutive qŷp))

  wc1 : - irŷ * (((-' (rŷp ⁻¹)) ⁻¹) .proj₁ *
                 ((-' (rŷp ⁻¹)) ⁻¹) .proj₁) ≡ - rŷv
  wc1 = Eq.trans (Eq.cong (λ t → - irŷ * (t * t))
      (Eq.trans (ineg (rŷp ⁻¹) (-' (rŷp ⁻¹)) Eq.refl)
        (Eq.cong -_ (inv-involutive rŷp))))
    (Eq.trans (Eq.cong (- irŷ *_) (negneg rŷv rŷv))
    (Eq.trans (Eq.sym (-‿distribˡ-* irŷ (rŷv * rŷv)))
      (Eq.cong -_ (Eq.trans (Eq.sym (*-assoc irŷ rŷv rŷv))
        (Eq.trans (Eq.cong (_* rŷv)
            (lemma-⁻¹ˡ (rŷp .proj₁) {{instRŷ}}))
          (*-identityˡ rŷv))))))

  wc2 : ((-' (₁ , λ ())) *' (-' (rŷp ⁻¹))) .proj₁ ≡ qŷp .proj₁
  wc2 = Eq.trans (negneg ₁ irŷ)
    (Eq.trans (*-identityˡ irŷ)
      (Eq.trans (iexp Y* A₂*) (*-comm iY (₁₊ a2'))))

  wc3 : (v₁v * (qŷv * qŷv)) * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁) ≡
        v₁v
  wc3 = begin
    (v₁v * (qŷv * qŷv)) * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁)
      ≡⟨ *-assoc v₁v (qŷv * qŷv) ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁) ⟩
    v₁v * ((qŷv * qŷv) * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁))
      ≡⟨ Eq.cong (v₁v *_) claim2 ⟩
    v₁v * ₁
      ≡⟨ *-identityʳ v₁v ⟩
    v₁v ∎
    where
    claim2 : (qŷv * qŷv) * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁) ≡ ₁
    claim2 = begin
      (qŷv * qŷv) * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁)
        ≡⟨ *-assoc qŷv qŷv ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁) ⟩
      qŷv * (qŷv * ((qŷp ⁻¹) .proj₁ * (qŷp ⁻¹) .proj₁))
        ≡⟨ Eq.cong (qŷv *_) (Eq.sym (*-assoc qŷv ((qŷp ⁻¹) .proj₁)
             ((qŷp ⁻¹) .proj₁))) ⟩
      qŷv * ((qŷv * (qŷp ⁻¹) .proj₁) * (qŷp ⁻¹) .proj₁)
        ≡⟨ Eq.cong (λ t → qŷv * (t * (qŷp ⁻¹) .proj₁))
             (lemma-⁻¹ʳ (qŷp .proj₁) {{instQŷ}}) ⟩
      qŷv * (₁ * (qŷp ⁻¹) .proj₁)
        ≡⟨ Eq.cong (qŷv *_) (*-identityˡ ((qŷp ⁻¹) .proj₁)) ⟩
      qŷv * (qŷp ⁻¹) .proj₁
        ≡⟨ lemma-⁻¹ʳ (qŷp .proj₁) {{instQŷ}} ⟩
      ₁ ∎

  wc4 : v₁v + - rŷv ≡ ₁
  wc4 = begin
    - ₁₊ a1' * iA₂ + - (₁₊ y * iA₂)
      ≡⟨ Eq.cong (- ₁₊ a1' * iA₂ +_) (-‿distribˡ-* (₁₊ y) iA₂) ⟩
    - ₁₊ a1' * iA₂ + - ₁₊ y * iA₂
      ≡⟨ Eq.sym (*-distribʳ-+ iA₂ (- ₁₊ a1') (- ₁₊ y)) ⟩
    (- ₁₊ a1' + - ₁₊ y) * iA₂
      ≡⟨ Eq.cong (_* iA₂) (Eq.trans (-‿+-comm (₁₊ a1') (₁₊ y))
           (Eq.trans (Eq.cong -_ wYA) (-‿involutive (₁₊ a2')))) ⟩
    ₁₊ a2' * iA₂
      ≡⟨ lemma-⁻¹ʳ (₁₊ a2') {{instA₂}} ⟩
    ₁ ∎

  wc5 : - irŷ + vyv ≡ ₁
  wc5 = begin
    - irŷ + - ₁₊ a1' * iY
      ≡⟨ Eq.cong (_+ - ₁₊ a1' * iY) (Eq.cong -_
           (Eq.trans (iexp Y* A₂*) (*-comm iY (₁₊ a2')))) ⟩
    - (₁₊ a2' * iY) + - ₁₊ a1' * iY
      ≡⟨ Eq.cong (_+ - ₁₊ a1' * iY) (-‿distribˡ-* (₁₊ a2') iY) ⟩
    - ₁₊ a2' * iY + - ₁₊ a1' * iY
      ≡⟨ Eq.sym (*-distribʳ-+ iY (- ₁₊ a2') (- ₁₊ a1')) ⟩
    (- ₁₊ a2' + - ₁₊ a1') * iY
      ≡⟨ Eq.cong (_* iY) (Eq.trans (-‿+-comm (₁₊ a2') (₁₊ a1'))
           (Eq.sym ySum)) ⟩
    ₁₊ y * iY
      ≡⟨ lemma-⁻¹ʳ (₁₊ y) {{instY}} ⟩
    ₁ ∎

  wc6 : u₁v + uyv ≡ ₁
  wc6 = begin
    - ₁₊ a2' * iA₁ + - ₁₊ y * iA₁
      ≡⟨ Eq.sym (*-distribʳ-+ iA₁ (- ₁₊ a2') (- ₁₊ y)) ⟩
    (- ₁₊ a2' + - ₁₊ y) * iA₁
      ≡⟨ Eq.cong (_* iA₁) (Eq.trans (-‿+-comm (₁₊ a2') (₁₊ y))
           (Eq.trans (Eq.cong -_ wYB) (-‿involutive (₁₊ a1')))) ⟩
    ₁₊ a1' * iA₁
      ≡⟨ lemma-⁻¹ʳ (₁₊ a1') {{instA₁}} ⟩
    ₁ ∎

  wiq : ((qŷp ⁻¹) .proj₁) ≡ rŷv
  wiq = Eq.trans (iexp A₂* Y*) (*-comm iA₂ (₁₊ y))

  wb3 : ((qŷp ⁻¹) *' (-' (₁ , λ ()))) .proj₁ ≡ (-' (qŷp ⁻¹)) .proj₁
  wb3 = Eq.trans (Eq.sym (-‿distribʳ-* ((qŷp ⁻¹) .proj₁) ₁))
    (Eq.cong -_ (*-identityʳ ((qŷp ⁻¹) .proj₁)))

  wPR : ((-' (qŷp ⁻¹)) *' (-' (rŷp ⁻¹))) .proj₁ ≡ ₁
  wPR = Eq.trans (negneg ((qŷp ⁻¹) .proj₁) irŷ)
    (Eq.trans (Eq.cong (_* irŷ) wiq)
      (lemma-⁻¹ʳ (rŷp .proj₁) {{instRŷ'}}))
    where
    instRŷ' = nztoℕ {y = rŷp .proj₁} {neq0 = rŷp .proj₂}

------------------------------------------------------------------------
-- The one-wire core: the two units and the H-tail annihilate.

module _ {m : ℕ} (a1' a2' y : Fin (₁₊ p-2))
  (ySum : ₁₊ y ≡ - (₁₊ a2' + ₁₊ a1')) where

  open PB ((₁₊ m) QRel,_===_)
  open PP ((₁₊ m) QRel,_===_)
  open SR word-setoid
  open BAValues a1' a2' y ySum
  open Lemmas0 m using (lemma-HH-M-1 ; lemma-S^k+l ; lemma-M1 ; aux-MM)

  midlow : S^ v₁v • (H ^ 3 • (ZM qŷp • (S^ rŷv • H))) ≈
           S • (H • S^ (- irŷ))
  midlow = begin
    S^ v₁v • (H ^ 3 • (ZM qŷp • (S^ rŷv • H)))
      ≈⟨ cright (trans (sym assoc) (trans (cleft (H3M qŷp)) assoc)) ⟩
    S^ v₁v • (ZM (qŷp ⁻¹) • (H ^ 3 • (S^ rŷv • H)))
      ≈⟨ cright (cright (trans assoc (trans (cright assoc)
           (sym assoc)))) ⟩
    S^ v₁v • (ZM (qŷp ⁻¹) • ((H • H) • (H • (S^ rŷv • H))))
      ≈⟨ cright (cright (cright (d7ε rŷp))) ⟩
    S^ v₁v • (ZM (qŷp ⁻¹) • ((H • H) •
      (S^ (- irŷ) • (ZM (-' (rŷp ⁻¹)) • (H • S^ (- irŷ))))))
      ≈⟨ cright (cright (cleft lemma-HH-M-1)) ⟩
    S^ v₁v • (ZM (qŷp ⁻¹) • (ZM (-' (₁ , λ ())) •
      (S^ (- irŷ) • (ZM (-' (rŷp ⁻¹)) • (H • S^ (- irŷ))))))
      ≈⟨ cright (trans (sym assoc)
           (cleft (Zmul (qŷp ⁻¹) (-' (₁ , λ ())) (-' (qŷp ⁻¹)) wb3))) ⟩
    S^ v₁v • (ZM (-' (qŷp ⁻¹)) •
      (S^ (- irŷ) • (ZM (-' (rŷp ⁻¹)) • (H • S^ (- irŷ)))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (SZmove (- irŷ) (-' (rŷp ⁻¹)) (- rŷv) wc1))
             assoc))) ⟩
    S^ v₁v • (ZM (-' (qŷp ⁻¹)) •
      (ZM (-' (rŷp ⁻¹)) • (S^ (- rŷv) • (H • S^ (- irŷ)))))
      ≈⟨ cright (trans (sym assoc) (trans (cleft
           (trans (Zmul (-' (qŷp ⁻¹)) (-' (rŷp ⁻¹)) (₁ , λ ()) wPR)
             (sym lemma-M1)))
           left-unit)) ⟩
    S^ v₁v • (S^ (- rŷv) • (H • S^ (- irŷ)))
      ≈⟨ trans (sym assoc) (cleft (trans (lemma-S^k+l v₁v (- rŷv))
           (refl' (Eq.cong S^ wc4)))) ⟩
    S • (H • S^ (- irŷ)) ∎

