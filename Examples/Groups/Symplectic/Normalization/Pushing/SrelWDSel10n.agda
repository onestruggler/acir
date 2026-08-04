------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case ββ: both shifted
-- slots are nonzero (witnesses y and z with z ≡ y + a₂ + a₁).  The two
-- sides do NOT match block-by-block: they differ by an S^δ that has to
-- cross the CZ (legal, since CZ commutes with lifted S-powers).  This
-- module proves the generic middle collapse and the two crossing
-- lemmas that realise it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

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
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime

------------------------------------------------------------------------
-- The generic middle collapse (midlow without the ySum hypothesis).

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open SR word-setoid
  open Lemmas0 j using (lemma-HH-M-1 ; lemma-S^k+l ; lemma-M1 ; aux-MM ;
                        lemma-S^kM)

  private
    negneg : ∀ (s t : ℤ ₚ) → - s * - t ≡ s * t
    negneg s t = Eq.trans (Eq.sym (-‿distribˡ-* s (- t)))
      (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribʳ-* s t)))
        (-‿involutive (s * t)))

  -- S-powers commute with H² (which is ZM(-1), whose square-inverse
  -- is 1).
  SkHH : ∀ (k : ℤ ₚ) → S^ k • (H • H) ≈ (H • H) • S^ k
  SkHH k =
    trans (cright lemma-HH-M-1)
    (trans (lemma-S^kM (- ₁) k ((-' (₁ , λ ())) .proj₂))
    (trans (cright (refl' (Eq.cong S^ valk)))
           (cleft (sym lemma-HH-M-1))))
    where
    i₁ = ((-' (₁ , λ ())) ⁻¹) .proj₁
    valk : k * (i₁ * i₁) ≡ k
    valk = Eq.trans (Eq.cong (λ t → k * (t * t)) aux-₁⁻¹)
      (Eq.trans (Eq.cong (k *_) aux-₁²) (*-identityʳ k))

  -- The ZM-annihilating middle: the unit ZM Q • S^ (Q⁻¹) is absorbed.
  midgen : ∀ (v : ℤ ₚ) (Q : ℤ* ₚ) →
    let q = Q .proj₁ ; iQ = (Q ⁻¹) .proj₁ in
    S^ v • (H ^ 3 • (ZM Q • (S^ ((Q ⁻¹) .proj₁) • H))) ≈
    S^ (v + - iQ) • (H • S^ (- q))
  midgen v Q = begin
    S^ v • (H ^ 3 • (ZM Q • (S^ ((Q ⁻¹) .proj₁) • H)))
      ≈⟨ cright (trans (sym assoc) (trans (cleft (H3M Q)) assoc)) ⟩
    S^ v • (ZM (Q ⁻¹) • (H ^ 3 • (S^ ((Q ⁻¹) .proj₁) • H)))
      ≈⟨ cright (cright (trans assoc (trans (cright assoc)
           (sym assoc)))) ⟩
    S^ v • (ZM (Q ⁻¹) • ((H • H) • (H • (S^ ((Q ⁻¹) .proj₁) • H))))
      ≈⟨ cright (cright (cright (d7ε (Q ⁻¹)))) ⟩
    S^ v • (ZM (Q ⁻¹) • ((H • H) •
      (S^ (- q') • (ZM (-' ((Q ⁻¹) ⁻¹)) • (H • S^ (- q'))))))
      ≈⟨ cright (cright (cleft lemma-HH-M-1)) ⟩
    S^ v • (ZM (Q ⁻¹) • (ZM (-' (₁ , λ ())) •
      (S^ (- q') • (ZM (-' ((Q ⁻¹) ⁻¹)) • (H • S^ (- q'))))))
      ≈⟨ cright (trans (sym assoc)
           (cleft (Zmul (Q ⁻¹) (-' (₁ , λ ())) (-' (Q ⁻¹)) vneg))) ⟩
    S^ v • (ZM (-' (Q ⁻¹)) •
      (S^ (- q') • (ZM (-' ((Q ⁻¹) ⁻¹)) • (H • S^ (- q')))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (SZmove (- q') (-' ((Q ⁻¹) ⁻¹))
             (- (Q ⁻¹) .proj₁) vsq)) assoc))) ⟩
    S^ v • (ZM (-' (Q ⁻¹)) • (ZM (-' ((Q ⁻¹) ⁻¹)) •
      (S^ (- (Q ⁻¹) .proj₁) • (H • S^ (- q')))))
      ≈⟨ cright (trans (sym assoc) (trans (cleft
           (trans (Zmul (-' (Q ⁻¹)) (-' ((Q ⁻¹) ⁻¹)) (₁ , λ ()) vone)
             (sym lemma-M1)))
           left-unit)) ⟩
    S^ v • (S^ (- (Q ⁻¹) .proj₁) • (H • S^ (- q')))
      ≈⟨ trans (sym assoc)
           (cleft (lemma-S^k+l v (- (Q ⁻¹) .proj₁))) ⟩
    S^ (v + - (Q ⁻¹) .proj₁) • (H • S^ (- q'))
      ≈⟨ cright (cright (refl'
           (Eq.cong (λ t → S^ (- t)) (inv-involutive Q)))) ⟩
    S^ (v + - (Q ⁻¹) .proj₁) • (H • S^ (- (Q .proj₁))) ∎
    where
    q' = ((Q ⁻¹) ⁻¹) .proj₁

    vneg : ((Q ⁻¹) *' (-' (₁ , λ ()))) .proj₁ ≡ (-' (Q ⁻¹)) .proj₁
    vneg = Eq.trans (Eq.sym (-‿distribʳ-* ((Q ⁻¹) .proj₁) ₁))
      (Eq.cong -_ (*-identityʳ ((Q ⁻¹) .proj₁)))

    iEv : ((-' ((Q ⁻¹) ⁻¹)) ⁻¹) .proj₁ ≡ - ((Q ⁻¹) .proj₁)
    iEv = Eq.trans (ineg ((Q ⁻¹) ⁻¹) (-' ((Q ⁻¹) ⁻¹)) Eq.refl)
      (Eq.cong -_ (inv-involutive (Q ⁻¹)))

    vsq : - q' * ((((-' ((Q ⁻¹) ⁻¹)) ⁻¹) .proj₁) *
                  (((-' ((Q ⁻¹) ⁻¹)) ⁻¹) .proj₁)) ≡ - (Q ⁻¹) .proj₁
    vsq = Eq.trans (Eq.cong (λ t → - q' * (t * t)) iEv)
      (Eq.trans (Eq.cong (- q' *_)
          (negneg ((Q ⁻¹) .proj₁) ((Q ⁻¹) .proj₁)))
      (Eq.trans (Eq.sym (-‿distribˡ-* q'
          (((Q ⁻¹) .proj₁) * ((Q ⁻¹) .proj₁))))
        (Eq.cong -_ claim)))
      where
      claim : q' * (((Q ⁻¹) .proj₁) * ((Q ⁻¹) .proj₁)) ≡ (Q ⁻¹) .proj₁
      claim = Eq.trans (Eq.sym (*-assoc q' ((Q ⁻¹) .proj₁)
          ((Q ⁻¹) .proj₁)))
        (Eq.trans (Eq.cong (_* ((Q ⁻¹) .proj₁))
            (lemma-⁻¹ˡ ((Q ⁻¹) .proj₁)
              {{nztoℕ {y = (Q ⁻¹) .proj₁} {neq0 = (Q ⁻¹) .proj₂}}}))
          (*-identityˡ ((Q ⁻¹) .proj₁)))

    vone : ((-' (Q ⁻¹)) *' (-' ((Q ⁻¹) ⁻¹))) .proj₁ ≡ ₁
    vone = Eq.trans (negneg ((Q ⁻¹) .proj₁) (((Q ⁻¹) ⁻¹) .proj₁))
      (lemma-⁻¹ʳ ((Q ⁻¹) .proj₁)
        {{nztoℕ {y = (Q ⁻¹) .proj₁} {neq0 = (Q ⁻¹) .proj₂}}})

------------------------------------------------------------------------
-- The two crossing lemmas.  The S^δ that separates the two sides is
-- produced by lem1 and consumed by lem2.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open SR word-setoid
  open Lemmas0 j using (lemma-S^k+l ; aux-MM)

  -- lem1 : the pre-CZ block, leaving S^δ on the right.
  lem1 : ∀ (Qz : ℤ* ₚ) →
    let qz = Qz .proj₁ ; izQ = (Qz ⁻¹) .proj₁ in
    (H • (S^ (- ((Qz ⁻¹) .proj₁)) • H)) • S⁻¹ ≈
    ZM Qz • (S^ ((Qz ⁻¹) .proj₁) • (H • S^ (Qz .proj₁ + - ₁)))
  lem1 Qz = begin
    (H • (S^ (- ((Qz ⁻¹) .proj₁)) • H)) • S⁻¹
      ≈⟨ cleft (d7ε X) ⟩
    (S^ (- ((X ⁻¹) .proj₁)) •
      (ZM (-' (X ⁻¹)) • (H • S^ (- ((X ⁻¹) .proj₁))))) • S⁻¹
      ≈⟨ cleft (cleft (refl' (Eq.cong S^ negX))) ⟩
    (S^ (Qz .proj₁) •
      (ZM (-' (X ⁻¹)) • (H • S^ (- ((X ⁻¹) .proj₁))))) • S⁻¹
      ≈⟨ cleft (cright (cleft
           (aux-MM ((-' (X ⁻¹)) .proj₂) (Qz .proj₂) negX))) ⟩
    (S^ (Qz .proj₁) • (ZM Qz • (H • S^ (- ((X ⁻¹) .proj₁))))) • S⁻¹
      ≈⟨ cleft (cright (cright (cright (refl' (Eq.cong S^ negX))))) ⟩
    (S^ (Qz .proj₁) • (ZM Qz • (H • S^ (Qz .proj₁)))) • S⁻¹
      ≈⟨ trans assoc (trans (cright assoc) (cright (cright assoc))) ⟩
    S^ (Qz .proj₁) • (ZM Qz • (H • (S^ (Qz .proj₁) • S⁻¹)))
      ≈⟨ cright (cright (cright (trans
           (cright (refl' (Eq.sym (SIfix {j}))))
           (lemma-S^k+l (Qz .proj₁) (- ₁))))) ⟩
    S^ (Qz .proj₁) • (ZM Qz • (H • S^ (Qz .proj₁ + - ₁)))
      ≈⟨ trans (sym assoc)
           (trans (cleft (SZmove (Qz .proj₁) Qz ((Qz ⁻¹) .proj₁) vmove))
             assoc) ⟩
    ZM Qz • (S^ ((Qz ⁻¹) .proj₁) • (H • S^ (Qz .proj₁ + - ₁))) ∎
    where
    X : ℤ* ₚ
    X = -' (Qz ⁻¹)

    negX : - ((X ⁻¹) .proj₁) ≡ Qz .proj₁
    negX = Eq.trans (Eq.cong -_
        (Eq.trans (ineg (Qz ⁻¹) X Eq.refl)
          (Eq.cong -_ (inv-involutive Qz))))
      (-‿involutive (Qz .proj₁))

    vmove : Qz .proj₁ * (((Qz ⁻¹) .proj₁) * ((Qz ⁻¹) .proj₁)) ≡
            (Qz ⁻¹) .proj₁
    vmove = Eq.trans (Eq.sym (*-assoc (Qz .proj₁) ((Qz ⁻¹) .proj₁)
        ((Qz ⁻¹) .proj₁)))
      (Eq.trans (Eq.cong (_* ((Qz ⁻¹) .proj₁))
          (lemma-⁻¹ʳ (Qz .proj₁)
            {{nztoℕ {y = Qz .proj₁} {neq0 = Qz .proj₂}}}))
        (*-identityˡ ((Qz ⁻¹) .proj₁)))

  -- lem2 : the post-CZ block, consuming the S^δ on the left.
  lem2 : ∀ (Qzy : ℤ* ₚ) (δ vz : ℤ ₚ) →
    δ + ((Qzy ⁻¹) .proj₁) ≡ vz →
    S^ δ • (H • (S^ (- (Qzy .proj₁)) • H ^ 3)) ≈
    S^ vz • (H ^ 3 • (ZM Qzy • S^ ((Qzy ⁻¹) .proj₁)))
  lem2 Qzy δ vz dv = begin
    S^ δ • (H • (S^ (- (Qzy .proj₁)) • H ^ 3))
      ≈⟨ cright (trans (cright (sym assoc)) (sym assoc)) ⟩
    S^ δ • ((H • (S^ (- (Qzy .proj₁)) • H)) • (H • H))
      ≈⟨ cright (cleft (d7ε Y)) ⟩
    S^ δ • ((S^ (- ((Y ⁻¹) .proj₁)) •
      (ZM (-' (Y ⁻¹)) • (H • S^ (- ((Y ⁻¹) .proj₁))))) • (H • H))
      ≈⟨ cright (cleft (cleft (refl' (Eq.cong S^ negY)))) ⟩
    S^ δ • ((S^ ((Qzy ⁻¹) .proj₁) •
      (ZM (-' (Y ⁻¹)) • (H • S^ (- ((Y ⁻¹) .proj₁))))) • (H • H))
      ≈⟨ cright (cleft (cright (cleft
           (aux-MM ((-' (Y ⁻¹)) .proj₂) ((Qzy ⁻¹) .proj₂) negY)))) ⟩
    S^ δ • ((S^ ((Qzy ⁻¹) .proj₁) •
      (ZM (Qzy ⁻¹) • (H • S^ (- ((Y ⁻¹) .proj₁))))) • (H • H))
      ≈⟨ cright (cleft (cright (cright (cright
           (refl' (Eq.cong S^ negY)))))) ⟩
    S^ δ • ((S^ ((Qzy ⁻¹) .proj₁) •
      (ZM (Qzy ⁻¹) • (H • S^ ((Qzy ⁻¹) .proj₁)))) • (H • H))
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (cright (cright assoc)))) ⟩
    S^ δ • (S^ ((Qzy ⁻¹) .proj₁) • (ZM (Qzy ⁻¹) •
      (H • (S^ ((Qzy ⁻¹) .proj₁) • (H • H)))))
      ≈⟨ cright (cright (cright (cright (SkHH ((Qzy ⁻¹) .proj₁))))) ⟩
    S^ δ • (S^ ((Qzy ⁻¹) .proj₁) • (ZM (Qzy ⁻¹) •
      (H • ((H • H) • S^ ((Qzy ⁻¹) .proj₁)))))
      ≈⟨ cright (cright (cright (sym assoc))) ⟩
    S^ δ • (S^ ((Qzy ⁻¹) .proj₁) • (ZM (Qzy ⁻¹) •
      (H ^ 3 • S^ ((Qzy ⁻¹) .proj₁))))
      ≈⟨ trans (sym assoc) (cleft (trans
           (lemma-S^k+l δ ((Qzy ⁻¹) .proj₁))
           (refl' (Eq.cong S^ dv)))) ⟩
    S^ vz • (ZM (Qzy ⁻¹) • (H ^ 3 • S^ ((Qzy ⁻¹) .proj₁)))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (H3M Qzy))) assoc)) ⟩
    S^ vz • (H ^ 3 • (ZM Qzy • S^ ((Qzy ⁻¹) .proj₁))) ∎
    where
    Y : ℤ* ₚ
    Y = -' Qzy

    negY : - ((Y ⁻¹) .proj₁) ≡ (Qzy ⁻¹) .proj₁
    negY = Eq.trans (Eq.cong -_ (ineg Qzy Y Eq.refl))
      (-‿involutive ((Qzy ⁻¹) .proj₁))


------------------------------------------------------------------------
-- The ββ value kit, under zySum : z ≡ y + (a₂ + a₁).

module BBValues (a1' a2' y z : Fin (₁₊ p-2))
  (zySum : ₁₊ z ≡ ₁₊ y + (₁₊ a2' + ₁₊ a1')) where

  A₁* A₂* Y* Z* : ℤ* ₚ
  A₁* = (₁₊ a1' , λ ())
  A₂* = (₁₊ a2' , λ ())
  Y*  = (₁₊ y , λ ())
  Z*  = (₁₊ z , λ ())

  iA₁ iA₂ iY iZ : ℤ ₚ
  iA₁ = (A₁* ⁻¹) .proj₁
  iA₂ = (A₂* ⁻¹) .proj₁
  iY  = (Y* ⁻¹) .proj₁
  iZ  = (Z* ⁻¹) .proj₁

  Qy* Qz* Qzy* : ℤ* ₚ
  Qy*  = A₂* *' (Y* ⁻¹)
  Qz*  = A₂* *' (Z* ⁻¹)
  Qzy* = Z* *' (Y* ⁻¹)

  u₁v v₁v uyv vyv uzv vzv : ℤ ₚ
  u₁v = - ₁₊ a2' * iA₁
  v₁v = - ₁₊ a1' * iA₂
  uyv = - ₁₊ y * iA₁
  vyv = - ₁₊ a1' * iY
  uzv = - ₁₊ z * iA₁
  vzv = - ₁₊ a1' * iZ

  private
    instA₁ = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instA₂ = nztoℕ {y = ₁₊ a2'} {neq0 = λ ()}
    instY  = nztoℕ {y = ₁₊ y} {neq0 = λ ()}
    instZ  = nztoℕ {y = ₁₊ z} {neq0 = λ ()}

  open Eq.≡-Reasoning

  -- The two additive rearrangements of zySum.
  wAY : ₁₊ a1' + ₁₊ y ≡ ₁₊ z + - ₁₊ a2'
  wAY = begin
    ₁₊ a1' + ₁₊ y
      ≡⟨ +-comm (₁₊ a1') (₁₊ y) ⟩
    ₁₊ y + ₁₊ a1'
      ≡⟨ Eq.sym (+-identityʳ (₁₊ y + ₁₊ a1')) ⟩
    (₁₊ y + ₁₊ a1') + ₀
      ≡⟨ Eq.cong ((₁₊ y + ₁₊ a1') +_) (Eq.sym (+-inverseʳ (₁₊ a2'))) ⟩
    (₁₊ y + ₁₊ a1') + (₁₊ a2' + - ₁₊ a2')
      ≡⟨ Eq.sym (+-assoc (₁₊ y + ₁₊ a1') (₁₊ a2') (- ₁₊ a2')) ⟩
    ((₁₊ y + ₁₊ a1') + ₁₊ a2') + - ₁₊ a2'
      ≡⟨ Eq.cong (_+ - ₁₊ a2') claim ⟩
    ₁₊ z + - ₁₊ a2' ∎
    where
    claim : (₁₊ y + ₁₊ a1') + ₁₊ a2' ≡ ₁₊ z
    claim = begin
      (₁₊ y + ₁₊ a1') + ₁₊ a2'
        ≡⟨ +-assoc (₁₊ y) (₁₊ a1') (₁₊ a2') ⟩
      ₁₊ y + (₁₊ a1' + ₁₊ a2')
        ≡⟨ Eq.cong (₁₊ y +_) (+-comm (₁₊ a1') (₁₊ a2')) ⟩
      ₁₊ y + (₁₊ a2' + ₁₊ a1')
        ≡⟨ Eq.sym zySum ⟩
      ₁₊ z ∎

  wA2Y : ₁₊ a2' + ₁₊ y ≡ ₁₊ z + - ₁₊ a1'
  wA2Y = begin
    ₁₊ a2' + ₁₊ y
      ≡⟨ +-comm (₁₊ a2') (₁₊ y) ⟩
    ₁₊ y + ₁₊ a2'
      ≡⟨ Eq.sym (+-identityʳ (₁₊ y + ₁₊ a2')) ⟩
    (₁₊ y + ₁₊ a2') + ₀
      ≡⟨ Eq.cong ((₁₊ y + ₁₊ a2') +_) (Eq.sym (+-inverseʳ (₁₊ a1'))) ⟩
    (₁₊ y + ₁₊ a2') + (₁₊ a1' + - ₁₊ a1')
      ≡⟨ Eq.sym (+-assoc (₁₊ y + ₁₊ a2') (₁₊ a1') (- ₁₊ a1')) ⟩
    ((₁₊ y + ₁₊ a2') + ₁₊ a1') + - ₁₊ a1'
      ≡⟨ Eq.cong (_+ - ₁₊ a1')
           (Eq.trans (+-assoc (₁₊ y) (₁₊ a2') (₁₊ a1'))
             (Eq.sym zySum)) ⟩
    ₁₊ z + - ₁₊ a1' ∎

  wZY : ₁₊ a2' + ₁₊ a1' ≡ ₁₊ z + - ₁₊ y
  wZY = begin
    ₁₊ a2' + ₁₊ a1'
      ≡⟨ Eq.sym (+-identityˡ (₁₊ a2' + ₁₊ a1')) ⟩
    ₀ + (₁₊ a2' + ₁₊ a1')
      ≡⟨ Eq.cong (_+ (₁₊ a2' + ₁₊ a1')) (Eq.sym (+-inverseˡ (₁₊ y))) ⟩
    (- ₁₊ y + ₁₊ y) + (₁₊ a2' + ₁₊ a1')
      ≡⟨ +-assoc (- ₁₊ y) (₁₊ y) (₁₊ a2' + ₁₊ a1') ⟩
    - ₁₊ y + (₁₊ y + (₁₊ a2' + ₁₊ a1'))
      ≡⟨ Eq.cong (- ₁₊ y +_) (Eq.sym zySum) ⟩
    - ₁₊ y + ₁₊ z
      ≡⟨ +-comm (- ₁₊ y) (₁₊ z) ⟩
    ₁₊ z + - ₁₊ y ∎

  -- The generic shape: -(t·i) + -(s·i) ≡ -((t+s)·i).
  private
    negsum : ∀ (t s i : ℤ ₚ) → - t * i + - s * i ≡ - ((t + s) * i)
    negsum t s i = begin
      - t * i + - s * i
        ≡⟨ Eq.sym (*-distribʳ-+ i (- t) (- s)) ⟩
      (- t + - s) * i
        ≡⟨ Eq.cong (_* i) (-‿+-comm t s) ⟩
      - (t + s) * i
        ≡⟨ Eq.sym (-‿distribˡ-* (t + s) i) ⟩
      - ((t + s) * i) ∎

    -- (w + -x)·i ≡ w·i + -₁ when x·i ≡ ₁.
    splitone : ∀ (w x i : ℤ ₚ) → x * i ≡ ₁ →
      (w + - x) * i ≡ w * i + - ₁
    splitone w x i xi = begin
      (w + - x) * i
        ≡⟨ *-distribʳ-+ i w (- x) ⟩
      w * i + - x * i
        ≡⟨ Eq.cong (w * i +_) (Eq.trans (Eq.sym (-‿distribˡ-* x i))
             (Eq.cong -_ xi)) ⟩
      w * i + - ₁ ∎

    splitneg : ∀ (w x i : ℤ ₚ) → (w + - x) * i ≡ w * i + - (x * i)
    splitneg w x i = Eq.trans (*-distribʳ-+ i w (- x))
      (Eq.cong (w * i +_) (Eq.sym (-‿distribˡ-* x i)))

    neg1 : ∀ (t : ℤ ₚ) → - (t + - ₁) + - ₁ ≡ - t
    neg1 t = begin
      - (t + - ₁) + - ₁
        ≡⟨ Eq.cong (_+ - ₁) (Eq.sym (-‿+-comm t (- ₁))) ⟩
      (- t + - - ₁) + - ₁
        ≡⟨ Eq.cong (λ u → (- t + u) + - ₁) (-‿involutive ₁) ⟩
      (- t + ₁) + - ₁
        ≡⟨ +-assoc (- t) ₁ (- ₁) ⟩
      - t + (₁ + - ₁)
        ≡⟨ Eq.cong (- t +_) (+-inverseʳ ₁) ⟩
      - t + ₀
        ≡⟨ +-identityʳ (- t) ⟩
      - t ∎

  αval : (v₁v + - (₁₊ y * iA₂)) + - ₁ ≡ - (₁₊ z * iA₂)
  αval = Eq.trans
    (Eq.cong (_+ - ₁)
      (Eq.trans (Eq.cong (v₁v +_)
          (-‿distribˡ-* (₁₊ y) iA₂))
      (Eq.trans (negsum (₁₊ a1') (₁₊ y) iA₂)
        (Eq.cong -_ (Eq.trans (Eq.cong (_* iA₂) wAY)
          (splitone (₁₊ z) (₁₊ a2') iA₂
            (lemma-⁻¹ʳ (₁₊ a2') {{instA₂}})))))))
    (neg1 (₁₊ z * iA₂))

  βval : (u₁v + uyv) + - ₁ ≡ uzv
  βval = Eq.trans
    (Eq.cong (_+ - ₁)
      (Eq.trans (negsum (₁₊ a2') (₁₊ y) iA₁)
        (Eq.cong -_ (Eq.trans (Eq.cong (_* iA₁) wA2Y)
          (splitone (₁₊ z) (₁₊ a1') iA₁
            (lemma-⁻¹ʳ (₁₊ a1') {{instA₁}}))))))
    (Eq.trans (neg1 (₁₊ z * iA₁))
      (-‿distribˡ-* (₁₊ z) iA₁))

  γval : - ₁ + (- (₁₊ a2' * iY) + vyv) ≡ - (₁₊ z * iY)
  γval = begin
    - ₁ + (- (₁₊ a2' * iY) + vyv)
      ≡⟨ Eq.cong (λ t → - ₁ + (t + vyv))
           (-‿distribˡ-* (₁₊ a2') iY) ⟩
    - ₁ + (- ₁₊ a2' * iY + - ₁₊ a1' * iY)
      ≡⟨ Eq.cong (- ₁ +_) (negsum (₁₊ a2') (₁₊ a1') iY) ⟩
    - ₁ + - ((₁₊ a2' + ₁₊ a1') * iY)
      ≡⟨ Eq.cong (λ t → - ₁ + - t)
           (Eq.trans (Eq.cong (_* iY) wZY)
             (splitone (₁₊ z) (₁₊ y) iY
               (lemma-⁻¹ʳ (₁₊ y) {{instY}}))) ⟩
    - ₁ + - (₁₊ z * iY + - ₁)
      ≡⟨ +-comm (- ₁) (- (₁₊ z * iY + - ₁)) ⟩
    - (₁₊ z * iY + - ₁) + - ₁
      ≡⟨ neg1 (₁₊ z * iY) ⟩
    - (₁₊ z * iY) ∎

  dval : ((₁₊ a2' * iZ) + - ₁) + (₁₊ y * iZ) ≡ vzv
  dval = begin
    ((₁₊ a2' * iZ) + - ₁) + (₁₊ y * iZ)
      ≡⟨ +-assoc (₁₊ a2' * iZ) (- ₁) (₁₊ y * iZ) ⟩
    (₁₊ a2' * iZ) + (- ₁ + (₁₊ y * iZ))
      ≡⟨ Eq.cong ((₁₊ a2' * iZ) +_) (+-comm (- ₁) (₁₊ y * iZ)) ⟩
    (₁₊ a2' * iZ) + ((₁₊ y * iZ) + - ₁)
      ≡⟨ Eq.sym (+-assoc (₁₊ a2' * iZ) (₁₊ y * iZ) (- ₁)) ⟩
    ((₁₊ a2' * iZ) + (₁₊ y * iZ)) + - ₁
      ≡⟨ Eq.cong (_+ - ₁) (Eq.sym (*-distribʳ-+ iZ (₁₊ a2') (₁₊ y))) ⟩
    ((₁₊ a2' + ₁₊ y) * iZ) + - ₁
      ≡⟨ Eq.cong (_+ - ₁) (Eq.trans (Eq.cong (_* iZ) wA2Y)
           (splitneg (₁₊ z) (₁₊ a1') iZ)) ⟩
    ((₁₊ z * iZ) + - (₁₊ a1' * iZ)) + - ₁
      ≡⟨ Eq.cong (λ t → (t + - (₁₊ a1' * iZ)) + - ₁)
           (lemma-⁻¹ʳ (₁₊ z) {{instZ}}) ⟩
    (₁ + - (₁₊ a1' * iZ)) + - ₁
      ≡⟨ Eq.cong (_+ - ₁) (+-comm ₁ (- (₁₊ a1' * iZ))) ⟩
    (- (₁₊ a1' * iZ) + ₁) + - ₁
      ≡⟨ +-assoc (- (₁₊ a1' * iZ)) ₁ (- ₁) ⟩
    - (₁₊ a1' * iZ) + (₁ + - ₁)
      ≡⟨ Eq.cong (- (₁₊ a1' * iZ) +_) (+-inverseʳ ₁) ⟩
    - (₁₊ a1' * iZ) + ₀
      ≡⟨ +-identityʳ (- (₁₊ a1' * iZ)) ⟩
    - (₁₊ a1' * iZ)
      ≡⟨ -‿distribˡ-* (₁₊ a1') iZ ⟩
    - ₁₊ a1' * iZ ∎


------------------------------------------------------------------------
-- The generic L-normalisation: two clause-4 pads around one hpad unit
-- collapse to the canonical form, whatever the values are.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-cong↑)

  private
    module L0u = Lemmas0 (₁₊ m)

    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    PAD : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    PAD u v = H • (h • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • h ^ 3)))))

    SkW : ∀ (k : ℤ ₚ) (w : Word (Gen (₁₊ m))) →
      S^ k • w ↑ ≈ w ↑ • S^ k
    SkW k w = comm⇒pow-comm {w = S} {v = w ↑} (toℕ k) 1
      (lemma-comm-S-w↑ w)

    SkCZ : ∀ (k : ℤ ₚ) → S^ k • CZ ≈ CZ • S^ k
    SkCZ k = comm⇒pow-comm {w = S} {v = CZ} (toℕ k) 1
      (sym (axiom comm-CZ-S↓))

    HW : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HW w = lemma-comm-H-w↑ w

    H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

    H4bot : H {₁₊ m} ^ 3 • H ≈ ε
    H4bot = trans assoc (trans (cright assoc) (axiom order-H))

    fixdownG : S⁻¹ {m} ↑ •
        (h • (S⁻¹ ↑ • (CZ • (h • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (h • (S⁻¹ ↑ • (CZ • (h • (S⁻¹ ↑ • S⁻¹)))))
    fixdownG = Eq.cong
      (λ u → S⁻¹ ↑ • (h • (S⁻¹ ↑ • (CZ • (h • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

  Lgen : ∀ (Q : ℤ* ₚ) (u₁ v₁ uy vy : ℤ ₚ) →
    PAD u₁ v₁ • ((ZM Q ↑ • S^ ((Q ⁻¹) .proj₁) ↑) • PAD uy vy) ≈
    H • (h • (S^ ((v₁ + - ((Q ⁻¹) .proj₁)) + - ₁) ↑ • (h • (S⁻¹ ↑ •
      (CZ • (h • (S^ (- ₁ + (- (Q .proj₁) + vy)) ↑ •
        (h ^ 3 • (S^ (- ₁ + (u₁ + uy)) • H ^ 3)))))))))
  Lgen Q u₁ v₁ uy vy = begin
    PAD u₁ v₁ • ((ZM Q ↑ • S^ iQ ↑) • PAD uy vy)
      ≈⟨ trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc))))))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (S^ v₁ ↑ •
      (h ^ 3 • ((ZM Q ↑ • S^ iQ ↑) • PAD uy vy)))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           assoc)))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (S^ v₁ ↑ • (h ^ 3 •
      (ZM Q ↑ • (S^ iQ ↑ • PAD uy vy))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans (sym assoc)
             (trans (cleft (sym (HW (S^ iQ)))) assoc))))))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (S^ v₁ ↑ • (h ^ 3 •
      (ZM Q ↑ • (H • (S^ iQ ↑ •
        (h • (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (HW (ZM Q)))) assoc)))))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (S^ v₁ ↑ • (h ^ 3 •
      (H • (ZM Q ↑ • (S^ iQ ↑ •
        (h • (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (HW (H ^ 3)))) assoc))))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (S^ v₁ ↑ • (H • (h ^ 3 •
      (ZM Q ↑ • (S^ iQ ↑ •
        (h • (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (HW (S^ v₁)))) assoc)))))) ⟩
    H • (h • (CZ • (S^ u₁ • (H ^ 3 • (H • (S^ v₁ ↑ • (h ^ 3 •
      (ZM Q ↑ • (S^ iQ ↑ •
        (h • (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc) (trans (cleft H4bot) left-unit))))) ⟩
    H • (h • (CZ • (S^ u₁ • (S^ v₁ ↑ • (h ^ 3 •
      (ZM Q ↑ • (S^ iQ ↑ •
        (h • (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))))
      ≈⟨ cright (cright (cright (cright (trans (cright
           (trans (cright (trans (cright (sym assoc)) (sym assoc)))
             (sym assoc)))
           (trans (sym assoc) (cleft midgenup)))))) ⟩
    H • (h • (CZ • (S^ u₁ • ((S^ (v₁ + - iQ) ↑ • (h • S^ (- q) ↑)) •
      (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (trans assoc
           (cright assoc))))) ⟩
    H • (h • (CZ • (S^ u₁ • (S^ (v₁ + - iQ) ↑ • (h • (S^ (- q) ↑ •
      (CZ • (S^ uy • (H ^ 3 • (S^ vy ↑ • h ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (sym (comm-CZ-S^↑ (- q))))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (sym (SkW uy (S^ (- q)))))
               (trans assoc (cright (trans (sym assoc)
                 (trans (cleft (sym (H3W (S^ (- q)))))
                 (trans assoc (cright (trans (sym assoc) (cleft (Sk+lup (- q) vy)))))))))))))))))))) ⟩
    H • (h • (CZ • (S^ u₁ • (S^ (v₁ + - iQ) ↑ • (h • (CZ • (S^ uy •
      (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3)))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (SkW u₁ (S^ (v₁ + - iQ))))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (SkW u₁ H))
             (trans assoc (cright (trans (sym assoc)
               (trans (cleft (SkCZ u₁))
               (trans assoc (cright (trans (sym assoc)
                 (cleft (L0u.lemma-S^k+l u₁ uy))))))))))))))))) ⟩
    H • (h • (CZ • (S^ (v₁ + - iQ) ↑ • (h • (CZ • (S^ (u₁ + uy) •
      (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3))))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (comm-CZ-S^↑ (v₁ + - iQ))) assoc))) ⟩
    H • (h • (S^ (v₁ + - iQ) ↑ • (CZ • (h • (CZ • (S^ (u₁ + uy) •
      (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3))))))))
      ≈⟨ cright (cright (cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownG))))))) ⟩
    H • (h • (S^ (v₁ + - iQ) ↑ •
      ((S⁻¹ ↑ • (h • (S⁻¹ ↑ • (CZ • (h • (S⁻¹ ↑ • S⁻¹)))))) •
        (S^ (u₁ + uy) • (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3))))))
      ≈⟨ cright (cright (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright (trans assoc (cright (trans assoc
               (cright assoc)))))))))))) ⟩
    H • (h • (S^ (v₁ + - iQ) ↑ • (S⁻¹ ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S⁻¹ ↑ • (S⁻¹ • (S^ (u₁ + uy) •
        (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3))))))))))))
      ≈⟨ cright (cright (trans (sym assoc) (cleft
           (trans (cright (refl' (Eq.cong _↑ (Eq.sym (SIfix {m})))))
             (Sk+lup (v₁ + - iQ) (- ₁)))))) ⟩
    H • (h • (S^ ((v₁ + - iQ) + - ₁) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S⁻¹ ↑ • (S⁻¹ • (S^ (u₁ + uy) •
        (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3)))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans (sym assoc)
             (cleft (trans (cleft (refl' (Eq.sym (SIfix {₁₊ m}))))
               (L0u.lemma-S^k+l (- ₁) (u₁ + uy))))))))))))  ⟩
    H • (h • (S^ ((v₁ + - iQ) + - ₁) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S⁻¹ ↑ • (S^ (- ₁ + (u₁ + uy)) •
        (H ^ 3 • (S^ (- q + vy) ↑ • h ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (trans
             (cright (trans (sym assoc)
               (trans (cleft (H3W (S^ (- q + vy))))
               (trans assoc (cright (H3W (H ^ 3)))))))
             (trans (sym assoc)
               (trans (cleft (SkW (- ₁ + (u₁ + uy)) (S^ (- q + vy))))
               (trans assoc
                 (trans (cright (sym assoc))
                 (trans (cright (cleft (SkW (- ₁ + (u₁ + uy)) (H ^ 3))))
                        (cright assoc))))))))))))))  ⟩
    H • (h • (S^ ((v₁ + - iQ) + - ₁) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S⁻¹ ↑ • (S^ (- q + vy) ↑ • (h ^ 3 •
        (S^ (- ₁ + (u₁ + uy)) • H ^ 3))))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (cleft (trans (cleft (refl' (Eq.cong _↑
                 (Eq.sym (SIfix {m})))))
               (Sk+lup (- ₁) (- q + vy)))))))))))  ⟩
    H • (h • (S^ ((v₁ + - iQ) + - ₁) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S^ (- ₁ + (- q + vy)) ↑ • (h ^ 3 •
        (S^ (- ₁ + (u₁ + uy)) • H ^ 3))))))))) ∎
    where
    q = Q .proj₁
    iQ = (Q ⁻¹) .proj₁

    midgenup : S^ v₁ ↑ • (h ^ 3 • (ZM Q ↑ • (S^ iQ ↑ • h))) ≈
               S^ (v₁ + - iQ) ↑ • (h • S^ (- q) ↑)
    midgenup = lemma-cong↑
      (S^ v₁ • (H ^ 3 • (ZM Q • (S^ iQ • H))))
      (S^ (v₁ + - iQ) • (H • S^ (- q)))
      (midgen v₁ Q)


------------------------------------------------------------------------
-- The generic R-normalisation: a unit, one pad and a second unit.
-- Pure commutation — no value conditions.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

  private
    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    PADr : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    PADr u v = H • (h • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • h ^ 3)))))

    SkW' : ∀ (k : ℤ ₚ) (w : Word (Gen (₁₊ m))) →
      S^ k • w ↑ ≈ w ↑ • S^ k
    SkW' k w = comm⇒pow-comm {w = S} {v = w ↑} (toℕ k) 1
      (lemma-comm-S-w↑ w)

    HW' : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HW' w = lemma-comm-H-w↑ w

    H3W' : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W' w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

  Rgen : ∀ (Qz Qzy : ℤ* ₚ) (ez ezy uz vz : ℤ ₚ) →
    (ZM Qz ↑ • S^ ez ↑) • (PADr uz vz • (ZM Qzy ↑ • S^ ezy ↑)) ≈
    H • (ZM Qz ↑ • (S^ ez ↑ • (h • (CZ •
      ((S^ vz ↑ • (h ^ 3 • (ZM Qzy ↑ • S^ ezy ↑))) • (S^ uz • H ^ 3))))))
  Rgen Qz Qzy ez ezy uz vz = begin
    (ZM Qz ↑ • S^ ez ↑) • (PADr uz vz • (ZM Qzy ↑ • S^ ezy ↑))
      ≈⟨ assoc ⟩
    ZM Qz ↑ • (S^ ez ↑ • (PADr uz vz • (ZM Qzy ↑ • S^ ezy ↑)))
      ≈⟨ cright (cright (trans assoc (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright (trans assoc (cright assoc))))))))))) ⟩
    ZM Qz ↑ • (S^ ez ↑ • (H • (h • (CZ • (S^ uz • (H ^ 3 •
      (S^ vz ↑ • (h ^ 3 • (ZM Qzy ↑ • S^ ezy ↑)))))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (HW' (S^ ez)))) assoc)) ⟩
    ZM Qz ↑ • (H • (S^ ez ↑ • (h • (CZ • (S^ uz • (H ^ 3 •
      (S^ vz ↑ • (h ^ 3 • (ZM Qzy ↑ • S^ ezy ↑)))))))))
      ≈⟨ trans (sym assoc) (trans (cleft (sym (HW' (ZM Qz)))) assoc) ⟩
    H • (ZM Qz ↑ • (S^ ez ↑ • (h • (CZ • (S^ uz • (H ^ 3 •
      (S^ vz ↑ • (h ^ 3 • (ZM Qzy ↑ • S^ ezy ↑)))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cright (H3W' TW))
           (trans (sym assoc)
           (trans (cleft (SkW' uz TW)) assoc))))))) ⟩
    H • (ZM Qz ↑ • (S^ ez ↑ • (h • (CZ •
      ((S^ vz ↑ • (h ^ 3 • (ZM Qzy ↑ • S^ ezy ↑))) •
        (S^ uz • H ^ 3)))))) ∎
    where
    TW : Word (Gen (₁₊ m))
    TW = S^ vz • (H ^ 3 • (ZM Qzy • S^ ezy))


------------------------------------------------------------------------
-- The ββ residual identity: Lgen normalises the left, Rgen the right,
-- and the two crossing lemmas move the surplus S^δ across the CZ.

module _ {m : ℕ} (a1' a2' y z : Fin (₁₊ p-2))
  (zySum : ₁₊ z ≡ ₁₊ y + (₁₊ a2' + ₁₊ a1')) where

  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open BBValues a1' a2' y z zySum
  open Lemmas-Sym using (lemma-cong↑)

  private
    h : Word (Gen (₂₊ m))
    h = H {m} ↑

    PADw : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    PADw u v = H • (h • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • h ^ 3)))))

    iQy iQz iQzy δv : ℤ ₚ
    iQy  = (Qy* ⁻¹) .proj₁
    iQz  = (Qz* ⁻¹) .proj₁
    iQzy = (Qzy* ⁻¹) .proj₁
    δv   = Qz* .proj₁ + - ₁

    iQyval : iQy ≡ ₁₊ y * iA₂
    iQyval = Eq.trans (iexp A₂* Y*) (*-comm iA₂ (₁₊ y))

    iQzval : iQz ≡ ₁₊ z * iA₂
    iQzval = Eq.trans (iexp A₂* Z*) (*-comm iA₂ (₁₊ z))

    iQzyval : iQzy ≡ ₁₊ y * iZ
    iQzyval = Eq.trans (iexp Z* Y*) (*-comm iZ (₁₊ y))

    αcast : (v₁v + - iQy) + - ₁ ≡ - iQz
    αcast = Eq.trans (Eq.cong (λ t → (v₁v + - t) + - ₁) iQyval)
      (Eq.trans αval (Eq.cong -_ (Eq.sym iQzval)))

    βcast : - ₁ + (u₁v + uyv) ≡ uzv
    βcast = Eq.trans (+-comm (- ₁) (u₁v + uyv)) βval

    dcast : δv + iQzy ≡ vzv
    dcast = Eq.trans (Eq.cong (δv +_) iQzyval) dval

    lem1up : (h • (S^ (- iQz) ↑ • h)) • S⁻¹ ↑ ≈
             ZM Qz* ↑ • (S^ iQz ↑ • (h • S^ δv ↑))
    lem1up = lemma-cong↑
      ((H • (S^ (- iQz) • H)) • S⁻¹)
      (ZM Qz* • (S^ iQz • (H • S^ δv)))
      (lem1 Qz*)

    lem2up : S^ δv ↑ • (h • (S^ (- (Qzy* .proj₁)) ↑ • h ^ 3)) ≈
             S^ vzv ↑ • (h ^ 3 • (ZM Qzy* ↑ • S^ iQzy ↑))
    lem2up = lemma-cong↑
      (S^ δv • (H • (S^ (- (Qzy* .proj₁)) • H ^ 3)))
      (S^ vzv • (H ^ 3 • (ZM Qzy* • S^ iQzy)))
      (lem2 Qzy* δv vzv dcast)

  idββ : PADw u₁v v₁v • ((ZM Qy* ↑ • S^ (₁₊ y * iA₂) ↑) • PADw uyv vyv) ≈
         (ZM Qz* ↑ • S^ (₁₊ z * iA₂) ↑) •
           (PADw uzv vzv • (ZM Qzy* ↑ • S^ (₁₊ y * iZ) ↑))
  idββ = begin
    PADw u₁v v₁v • ((ZM Qy* ↑ • S^ (₁₊ y * iA₂) ↑) • PADw uyv vyv)
      ≈⟨ cright (cleft (cright (refl'
           (Eq.cong (λ t → S^ t ↑) (Eq.sym iQyval))))) ⟩
    PADw u₁v v₁v • ((ZM Qy* ↑ • S^ iQy ↑) • PADw uyv vyv)
      ≈⟨ Lgen Qy* u₁v v₁v uyv vyv ⟩
    H • (h • (S^ ((v₁v + - iQy) + - ₁) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S^ (- ₁ + (- (Qy* .proj₁) + vyv)) ↑ •
        (h ^ 3 • (S^ (- ₁ + (u₁v + uyv)) • H ^ 3)))))))))
      ≈⟨ cright (cright (cleft (refl'
           (Eq.cong (λ t → S^ t ↑) αcast)))) ⟩
    H • (h • (S^ (- iQz) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S^ (- ₁ + (- (Qy* .proj₁) + vyv)) ↑ •
        (h ^ 3 • (S^ (- ₁ + (u₁v + uyv)) • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cleft (refl' (Eq.cong (λ t → S^ t ↑) γval))))))))) ⟩
    H • (h • (S^ (- iQz) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ •
        (h ^ 3 • (S^ (- ₁ + (u₁v + uyv)) • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (cright (cright (cleft (refl'
             (Eq.cong S^ βcast)))))))))))  ⟩
    H • (h • (S^ (- iQz) ↑ • (h • (S⁻¹ ↑ • (CZ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ • (h ^ 3 • (S^ uzv • H ^ 3)))))))))
      ≈⟨ cright (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (cright (sym assoc)))
                  (cleft (sym assoc)))))) ⟩
    H • (((h • (S^ (- iQz) ↑ • h)) • S⁻¹ ↑) • (CZ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ • (h ^ 3 • (S^ uzv • H ^ 3))))))
      ≈⟨ cright (cleft lem1up) ⟩
    H • ((ZM Qz* ↑ • (S^ iQz ↑ • (h • S^ δv ↑))) • (CZ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ • (h ^ 3 • (S^ uzv • H ^ 3))))))
      ≈⟨ cright (trans assoc (trans (cright assoc)
           (cright (cright assoc)))) ⟩
    H • (ZM Qz* ↑ • (S^ iQz ↑ • (h • (S^ δv ↑ • (CZ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ • (h ^ 3 • (S^ uzv • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (comm-CZ-S^↑ δv))) assoc))))) ⟩
    H • (ZM Qz* ↑ • (S^ iQz ↑ • (h • (CZ • (S^ δv ↑ • (h •
      (S^ (- (Qzy* .proj₁)) ↑ • (h ^ 3 • (S^ uzv • H ^ 3)))))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc)) (sym assoc))))))) ⟩
    H • (ZM Qz* ↑ • (S^ iQz ↑ • (h • (CZ •
      ((S^ δv ↑ • (h • (S^ (- (Qzy* .proj₁)) ↑ • h ^ 3))) •
        (S^ uzv • H ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright (cleft lem2up))))) ⟩
    H • (ZM Qz* ↑ • (S^ iQz ↑ • (h • (CZ •
      ((S^ vzv ↑ • (h ^ 3 • (ZM Qzy* ↑ • S^ iQzy ↑))) •
        (S^ uzv • H ^ 3))))))
      ≈⟨ sym (Rgen Qz* Qzy* iQz iQzy uzv vzv) ⟩
    (ZM Qz* ↑ • S^ iQz ↑) • (PADw uzv vzv • (ZM Qzy* ↑ • S^ iQzy ↑))
      ≈⟨ cleft (cright (refl' (Eq.cong (λ t → S^ t ↑) iQzval))) ⟩
    (ZM Qz* ↑ • S^ (₁₊ z * iA₂) ↑) •
      (PADw uzv vzv • (ZM Qzy* ↑ • S^ iQzy ↑))
      ≈⟨ cright (cright (cright (refl'
           (Eq.cong (λ t → S^ t ↑) iQzyval)))) ⟩
    (ZM Qz* ↑ • S^ (₁₊ z * iA₂) ↑) •
      (PADw uzv vzv • (ZM Qzy* ↑ • S^ (₁₊ y * iZ) ↑)) ∎

