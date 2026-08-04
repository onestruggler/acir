------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₀,₁₊b1')/(₁₊a2',b2), branch β:
-- the middle slot b₁ - a₂ is some ₁₊x, so both CZ's hit clause 4 and
-- the second bottom-H escapes as a full Borel pad ZM Q • S^(Q⁻¹).
-- Everything rests on one width-generic conjugation law, tstar.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11c
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
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime
  using (↓-pow-S ; H↑3H↑≈ε ; comm-up₂ ; comm-Spow-↑ ; comm-ZM-↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10c
  p-2 p-prime using (H3M ; d7ε)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  p-2 p-prime using (SkHH)

------------------------------------------------------------------------
-- The conjugation law.  Pushing H past S^(-Q) turns it into the Borel
-- pad the H-escape table produces: S^(Q⁻¹) • H³ • ZM Q • S^(Q⁻¹).

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open Lemmas0 j using (aux-MM)
  open SR word-setoid

  tstar : ∀ (Q : ℤ* ₚ) →
    H • (S^ (- (Q .proj₁)) • H ^ 3) ≈
    S^ ((Q ⁻¹) .proj₁) • (H ^ 3 • (ZM Q • S^ ((Q ⁻¹) .proj₁)))
  tstar Q = begin
    H • (S^ (- (Q .proj₁)) • H ^ 3)
      ≈⟨ trans (cright (sym assoc)) (sym assoc) ⟩
    (H • (S^ (- (Q .proj₁)) • H)) • (H • H)
      ≈⟨ cleft (trans (d7ε (-' Q)) fix1) ⟩
    (S^ e • (ZM (Q ⁻¹) • (H • S^ e))) • (H • H)
      ≈⟨ assoc ⟩
    S^ e • ((ZM (Q ⁻¹) • (H • S^ e)) • (H • H))
      ≈⟨ cright (trans assoc (cright (trans assoc
           (trans (cright (SkHH e)) (sym assoc))))) ⟩
    S^ e • (ZM (Q ⁻¹) • ((H • (H • H)) • S^ e))
      ≈⟨ cright (trans (sym assoc) (trans (cleft (sym (H3M Q))) assoc)) ⟩
    S^ e • (H ^ 3 • (ZM Q • S^ e)) ∎
    where
    e = (Q ⁻¹) .proj₁

    vE : - (((-' Q) ⁻¹) .proj₁) ≡ e
    vE = Eq.trans (Eq.cong -_ (inv-neg-comm Q)) (-‿involutive e)

    fix1 : S^ (- (((-' Q) ⁻¹) .proj₁)) •
             (ZM (-' ((-' Q) ⁻¹)) • (H • S^ (- (((-' Q) ⁻¹) .proj₁)))) ≈
           S^ e • (ZM (Q ⁻¹) • (H • S^ e))
    fix1 = cong (refl' (Eq.cong S^ vE))
      (cong (aux-MM ((-' ((-' Q) ⁻¹)) .proj₂) ((Q ⁻¹) .proj₂) vE)
        (cright (refl' (Eq.cong S^ vE))))

------------------------------------------------------------------------
-- The branch-β residual identity, at width ₂₊ m.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)
  open Lemmas0 (₁₊ m) using (lemma-S^k+l)

  private
    W3c : Word (Gen (₂₊ m))
    W3c = H ↑ • (CZ • (H ↑) ^ 3)

    PADc : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    PADc u w =
      H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ w ↑ • (H ↑) ^ 3)))))

    HWc : ∀ (w : Word (Gen (₁₊ m))) → H • w ↑ ≈ w ↑ • H
    HWc w = lemma-comm-H-w↑ w

    SinvHc : S⁻¹ • H ↑ ≈ H ↑ • S⁻¹
    SinvHc = comm⇒pow-comm {w = S} {v = H ↑} p-1 1
      (lemma-comm-S-w↑ H)

    SdownCZc : S⁻¹ • CZ ≈ CZ • S⁻¹
    SdownCZc = comm⇒pow-comm {w = S} {v = CZ} p-1 1
      (sym (axiom comm-CZ-S↓))

    SupH3c : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3c = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    fixdownc : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdownc = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

    -- Merging an S⁻¹ into an S-power, on either wire.
    mergeS : ∀ (k : ℤ ₚ) → S⁻¹ • S^ k ≈ S^ (- ₁ + k)
    mergeS k =
      trans (refl' (Eq.cong (_• S^ k) (Eq.sym SIfix)))
        (lemma-S^k+l (- ₁) k)

    mergeSup : ∀ (k : ℤ ₚ) → S⁻¹ {m} ↑ • S^ k ↑ ≈ S^ (- ₁ + k) ↑
    mergeSup k = lemma-cong↑ (S⁻¹ • S^ k) (S^ (- ₁ + k))
      (PBm.trans (PBm.refl' (Eq.cong (_• S^ k) (Eq.sym SIfix)))
        (L0m.lemma-S^k+l (- ₁) k))
      where module PBm = PB ((₁₊ m) QRel,_===_)
            module L0m = Lemmas0 m

  -- The wire-separated core: everything after the second CZ.
  xcore : ∀ (Q : ℤ* ₚ) (v : ℤ ₚ) →
    S⁻¹ • (H • (S⁻¹ • (S⁻¹ ↑ • (S^ (₁ + - (Q .proj₁)) •
      (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3)))))) ≈
    S^ (- ₁ + (Q ⁻¹) .proj₁) • (H ^ 3 • (S^ (- ₁ + v) ↑ •
      ((H ↑) ^ 3 • (ZM Q • S^ ((Q ⁻¹) .proj₁)))))
  xcore Q v = begin
    S⁻¹ • (H • (S⁻¹ • (S⁻¹ ↑ • (S^ (₁ + - q) •
      (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (comm-Spow-↑ (toℕ (₁ + - q)) S⁻¹)))
             assoc)))) ⟩
    S⁻¹ • (H • (S⁻¹ • (S^ (₁ + - q) • (S⁻¹ ↑ •
      (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft SupH3c) assoc))))) ⟩
    S⁻¹ • (H • (S⁻¹ • (S^ (₁ + - q) • (H ^ 3 • (S⁻¹ ↑ •
      (S^ v ↑ • (H ↑) ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft (mergeSup v))))))) ⟩
    S⁻¹ • (H • (S⁻¹ • (S^ (₁ + - q) • (H ^ 3 •
      (S^ (- ₁ + v) ↑ • (H ↑) ^ 3)))))
      ≈⟨ cright (cright (trans (sym assoc)
           (cleft (trans (mergeS (₁ + - q))
             (refl' (Eq.cong S^ vmerge)))))) ⟩
    S⁻¹ • (H • (S^ (- q) • (H ^ 3 •
      (S^ (- ₁ + v) ↑ • (H ↑) ^ 3))))
      ≈⟨ cright (trans (cright (sym assoc)) (sym assoc)) ⟩
    S⁻¹ • ((H • (S^ (- q) • H ^ 3)) •
      (S^ (- ₁ + v) ↑ • (H ↑) ^ 3))
      ≈⟨ cright (cleft (tstar Q)) ⟩
    S⁻¹ • ((S^ e • (H ^ 3 • (ZM Q • S^ e))) •
      (S^ (- ₁ + v) ↑ • (H ↑) ^ 3))
      ≈⟨ cright (trans assoc (cright (trans assoc
           (cright (trans comm-ZM-S↑ assoc))))) ⟩
    S⁻¹ • (S^ e • (H ^ 3 • (S^ (- ₁ + v) ↑ •
      ((H ↑) ^ 3 • (ZM Q • S^ e)))))
      ≈⟨ trans (sym assoc) (cleft (mergeS e)) ⟩
    S^ (- ₁ + e) • (H ^ 3 • (S^ (- ₁ + v) ↑ •
      ((H ↑) ^ 3 • (ZM Q • S^ e)))) ∎
    where
    q = Q .proj₁
    e = (Q ⁻¹) .proj₁

    vmerge : - ₁ + (₁ + - q) ≡ - q
    vmerge = Eq.trans (Eq.sym (+-assoc (- ₁) ₁ (- q)))
      (Eq.trans (Eq.cong (_+ - q) (+-inverseˡ ₁)) (+-identityˡ (- q)))

    comm-ZM-S↑ : (ZM Q • S^ e) • (S^ (- ₁ + v) • H ^ 3) ↑ ≈
                 (S^ (- ₁ + v) • H ^ 3) ↑ • (ZM Q • S^ e)
    comm-ZM-S↑ = comm-up₂ (S^ (- ₁ + v) • H ^ 3)
      (comm-ZM-↑ Q (S^ (- ₁ + v) • H ^ 3))
      (comm-Spow-↑ (toℕ e) (S^ (- ₁ + v) • H ^ 3))

  idc11c : ∀ (Q : ℤ* ₚ) (v : ℤ ₚ) →
    W3c • PADc (₁ + - (Q .proj₁)) v ≈
    S⁻¹ • (PADc (- ₁ + (Q ⁻¹) .proj₁) (- ₁ + v) •
      (ZM Q • S^ ((Q ⁻¹) .proj₁)))
  idc11c Q v = begin
    W3c • PADc (₁ + - q) v
      ≈⟨ trans assoc (cright assoc) ⟩
    H ↑ • (CZ • ((H ↑) ^ 3 • PADc (₁ + - q) v))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (sym (HWc (H ^ 3))))
           (trans assoc
           (trans (cright (sym assoc))
           (trans (cright (cleft H↑3H↑≈ε)) (cright left-unit))))))) ⟩
    H ↑ • (CZ • (H • (CZ • T)))
      ≈⟨ cright (trans (cright (sym assoc)) (sym assoc)) ⟩
    H ↑ • ((CZ • (H • CZ)) • T)
      ≈⟨ cright (cleft (trans (axiom selinger-c11) (refl' fixdownc))) ⟩
    H ↑ • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))) • T)
      ≈⟨ cright (trans assoc (cright (trans assoc (cright (trans assoc
           (cright (trans assoc (cright (trans assoc
             (cright assoc)))))))))) ⟩
    H ↑ • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • (S⁻¹ ↑ • T)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft SdownCZc) assoc)))) ⟩
    H ↑ • (S⁻¹ • (H • (CZ • (S⁻¹ • (H • (S⁻¹ • (S⁻¹ ↑ • T)))))))
      ≈⟨ trans (sym assoc) (trans (cleft (sym SinvHc)) assoc) ⟩
    S⁻¹ • (H ↑ • (H • (CZ • (S⁻¹ • (H • (S⁻¹ • (S⁻¹ ↑ • T)))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (HWc H))) assoc)) ⟩
    S⁻¹ • (H • (H ↑ • (CZ • (S⁻¹ • (H • (S⁻¹ • (S⁻¹ ↑ • T)))))))
      ≈⟨ cright (cright (cright (cright (xcore Q v)))) ⟩
    S⁻¹ • (H • (H ↑ • (CZ • (S^ (- ₁ + e) • (H ^ 3 •
      (S^ (- ₁ + v) ↑ • ((H ↑) ^ 3 • (ZM Q • S^ e))))))))
      ≈⟨ sym (cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright
             (trans assoc (cright assoc))))))))))) ⟩
    S⁻¹ • (PADc (- ₁ + e) (- ₁ + v) • (ZM Q • S^ e)) ∎
    where
    q = Q .proj₁
    e = (Q ⁻¹) .proj₁
    T = S^ (₁ + - (Q .proj₁)) •
          (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3))
