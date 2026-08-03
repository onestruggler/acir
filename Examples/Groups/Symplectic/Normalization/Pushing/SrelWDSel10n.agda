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
