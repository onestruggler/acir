------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₁₊a1',₁₊b1'')/(₀,b2), branch β:
-- all three H-escapes are full Borel pads, but each one sits in the
-- midgen pattern H³ • ZM Q • S^(Q⁻¹) • H, so every ZM collapses and no
-- CZ-power ever appears.  Both sides then meet at a common normal form.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11g
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
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; comm-Spow-↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  p-2 p-prime using (midgen)

------------------------------------------------------------------------
-- The branch-β residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑)
  open Lemmas0 (₁₊ m) using (lemma-S^k+l)

  private
    WDg : Word (Gen (₂₊ m))
    WDg = H • (CZ • H ^ 3)

    -- The common normal form both sides reduce to.
    NFg : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    NFg s t =
      H • (S^ s • (H • (S⁻¹ • (CZ • (H • (S^ t • (H ^ 3 • S⁻¹ ↑)))))))

    czS : ∀ (t : ℤ ₚ) → S^ t • CZ ≈ CZ • S^ t
    czS t = comm⇒pow-comm {w = S} {v = CZ} (toℕ t) 1
      (sym (axiom comm-CZ-S↓))

    SupH3g : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3g = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    mgR : ∀ (t : ℤ ₚ) → S^ t • S⁻¹ ≈ S^ (t + - ₁)
    mgR t =
      trans (refl' (Eq.cong (S^ t •_) (Eq.sym SIfix)))
        (lemma-S^k+l t (- ₁))

    mgL : ∀ (t : ℤ ₚ) → S⁻¹ • S^ t ≈ S^ (- ₁ + t)
    mgL t =
      trans (refl' (Eq.cong (_• S^ t) (Eq.sym SIfix)))
        (lemma-S^k+l (- ₁) t)

    fixdowng : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdowng = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

    -- midgen with no leading S-power.
    mid0 : ∀ (Q : ℤ* ₚ) →
      H ^ 3 • (ZM Q • (S^ ((Q ⁻¹) .proj₁) • H)) ≈
      S^ (- ((Q ⁻¹) .proj₁)) • (H • S^ (- (Q .proj₁)))
    mid0 Q =
      trans (sym left-unit)
      (trans (midgen ₀ Q)
        (cleft (refl' (Eq.cong S^
          (+-identityˡ (- ((Q ⁻¹) .proj₁)))))))

    -- The same collapse with the trailing H moved to an H³ on the
    -- right, which is the shape the R-side pad arrives in.
    tailfix : ∀ (Q : ℤ* ₚ) →
      H ^ 3 • (ZM Q • S^ ((Q ⁻¹) .proj₁)) ≈
      S^ (- ((Q ⁻¹) .proj₁)) • (H • (S^ (- (Q .proj₁)) • H ^ 3))
    tailfix Q =
      trans (sym right-unit)
      (trans (cright (sym (axiom order-H)))
      (trans (trans assoc (trans (cright assoc)
        (trans (cright (cright (sym assoc)))
        (trans (cright (sym assoc)) (sym assoc)))))
      (trans (cleft (mid0 Q))
        (trans assoc (cright assoc)))))

  -- The left side.
  leftg : ∀ (QL : ℤ* ₚ) →
    WDg • ((ZM QL • S^ ((QL ⁻¹) .proj₁)) • WDg) ≈
    NFg (- ((QL ⁻¹) .proj₁) + - ₁) (- ₁ + - (QL .proj₁))
  leftg QL = begin
    WDg • ((ZM QL • S^ iQL) • WDg)
      ≈⟨ trans assoc (trans (cright assoc)
           (cright (cright (cright assoc)))) ⟩
    H • (CZ • (H ^ 3 • (ZM QL • (S^ iQL • (H • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc)) (sym assoc)))) ⟩
    H • (CZ • ((H ^ 3 • (ZM QL • (S^ iQL • H))) • (CZ • H ^ 3)))
      ≈⟨ cright (cright (cleft (mid0 QL))) ⟩
    H • (CZ • ((S^ (- iQL) • (H • S^ (- qL))) • (CZ • H ^ 3)))
      ≈⟨ cright (cright (trans assoc (trans (cright assoc)
           (cright (cright (trans (sym assoc)
             (trans (cleft (czS (- qL))) assoc))))))) ⟩
    H • (CZ • (S^ (- iQL) • (H • (CZ • (S^ (- qL) • H ^ 3)))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (czS (- iQL)))) assoc)) ⟩
    H • (S^ (- iQL) • (CZ • (H • (CZ • (S^ (- qL) • H ^ 3)))))
      ≈⟨ cright (cright (trans (cright (sym assoc))
           (trans (sym assoc)
             (cleft (trans (axiom selinger-c11) (refl' fixdowng)))))) ⟩
    H • (S^ (- iQL) • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))))
      • (S^ (- qL) • H ^ 3)))
      ≈⟨ cright (cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright (trans assoc
             (cright assoc))))))))))) ⟩
    H • (S^ (- iQL) • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S^ (- qL) • H ^ 3)))))))))
      ≈⟨ cright (trans (sym assoc) (cleft (mgR (- iQL)))) ⟩
    H • (S^ (- iQL + - ₁) • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S^ (- qL) • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (cright (trans (sym assoc)
             (trans (cleft (sym (comm-Spow-↑ (toℕ (- qL)) S⁻¹)))
               assoc)))
           (trans (trans (sym assoc) (cleft (mgL (- qL))))
             (cright SupH3g)))))))) ⟩
    NFg (- iQL + - ₁) (- ₁ + - qL) ∎
    where
    qL = QL .proj₁
    iQL = (QL ⁻¹) .proj₁

  -- The right side.
  rightg : ∀ (QL Q2 Q5 : ℤ* ₚ) →
    (Q2 ⁻¹) .proj₁ ≡ ₁ + (QL ⁻¹) .proj₁ →
    Q2 .proj₁ ≡ ₁ + - ((Q5 ⁻¹) .proj₁) →
    Q5 .proj₁ ≡ ₁ + QL .proj₁ →
    (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
      (WDg • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • S⁻¹ ↑)) ≈
    NFg (- ((QL ⁻¹) .proj₁) + - ₁) (- ₁ + - (QL .proj₁))
  rightg QL Q2 Q5 h2 h2' h5 = begin
    (ZM Q2 • S^ iQ2) • (WDg • ((ZM Q5 • S^ iQ5) • S⁻¹ ↑))
      ≈⟨ trans assoc (cright (cright (trans assoc (cright assoc)))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (CZ • (H ^ 3 •
      ((ZM Q5 • S^ iQ5) • S⁻¹ ↑)))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc)
           (trans (cleft (tailfix Q5))
             (trans assoc (cright (trans assoc (cright assoc))))))))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (CZ • (S^ (- iQ5) •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (czS (- iQ5)))) assoc)))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ trans (sym left-unit)
           (trans (cleft (sym (axiom order-H))) assoc) ⟩
    H • (H ^ 3 • (ZM Q2 • (S^ iQ2 • (H • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))))
      ≈⟨ cright (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (mid0 Q2))
             (trans assoc (cright assoc)))))) ⟩
    H • (S^ (- iQ2) • (H • (S^ (- q2) • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (cleft (trans (lemma-S^k+l (- q2) (- iQ5))
             (refl' (Eq.trans (Eq.cong S^ vB) SIfix))))))) ⟩
    H • (S^ (- iQ2) • (H • (S⁻¹ • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ trans (cright (cleft (refl' (Eq.cong S^ vA))))
           (cright (cright (cright (cright (cright (cright
             (cleft (refl' (Eq.cong S^ vC))))))))) ⟩
    NFg (- iQL + - ₁) (- ₁ + - qL) ∎
    where
    qL = QL .proj₁
    iQL = (QL ⁻¹) .proj₁
    q2 = Q2 .proj₁
    iQ2 = (Q2 ⁻¹) .proj₁
    q5 = Q5 .proj₁
    iQ5 = (Q5 ⁻¹) .proj₁

    vA : - iQ2 ≡ - iQL + - ₁
    vA = Eq.trans (Eq.cong -_ h2)
      (Eq.trans (Eq.sym (-‿+-comm ₁ iQL)) (+-comm (- ₁) (- iQL)))

    vB : - q2 + - iQ5 ≡ - ₁
    vB = Eq.trans (Eq.cong (λ t → - t + - iQ5) h2')
      (Eq.trans (Eq.cong (_+ - iQ5)
          (Eq.trans (Eq.sym (-‿+-comm ₁ (- iQ5)))
            (Eq.cong (- ₁ +_) (-‿involutive iQ5))))
      (Eq.trans (+-assoc (- ₁) iQ5 (- iQ5))
      (Eq.trans (Eq.cong (- ₁ +_) (+-inverseʳ iQ5))
        (+-identityʳ (- ₁)))))

    vC : - q5 ≡ - ₁ + - qL
    vC = Eq.trans (Eq.cong -_ h5) (Eq.sym (-‿+-comm ₁ qL))

  id11g : ∀ (QL Q2 Q5 : ℤ* ₚ) →
    (Q2 ⁻¹) .proj₁ ≡ ₁ + (QL ⁻¹) .proj₁ →
    Q2 .proj₁ ≡ ₁ + - ((Q5 ⁻¹) .proj₁) →
    Q5 .proj₁ ≡ ₁ + QL .proj₁ →
    WDg • ((ZM QL • S^ ((QL ⁻¹) .proj₁)) • WDg) ≈
    (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
      (WDg • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • S⁻¹ ↑))
  id11g QL Q2 Q5 h2 h2' h5 =
    trans (leftg QL) (sym (rightg QL Q2 Q5 h2 h2' h5))
