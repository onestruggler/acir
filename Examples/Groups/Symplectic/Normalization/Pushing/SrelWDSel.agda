------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger-relation cases of srel-wd on deep inj₂ cosets.  c12 on a
-- triply-inj₂ coset: the lifted CZ threads the lower box pair via
-- ract-↑-≡ and the escapes commute through the axiom.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel
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
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-CZ-w↑ ; lemma-cong↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0#)

import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2 p-2 p-prime
  using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ p-2 p-prime
  using (H↑3H↑≈ε)

------------------------------------------------------------------------
-- c12 on a triply-inj₂ coset, all-zero a-slots: every escape is the
-- CZ letter itself and the residual is the axiom.

module _ {m : ℕ} where
  open PB ((₃₊ m) QRel,_===_)

  private
    ract3 = ract {₃₊ m}

  c12-go-000 : ∀ (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
    ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
      (CZ ↑ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
      (CZ • CZ ↑))
  c12-go-000 b1 b2 b3 lm3 = resid≈ , coset≡
    where
    lm : C (₃₊ m)
    lm = inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))

    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₁
    resid≈ =
      trans (refl' (Eq.cong
          (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
          (ract-↑-≡ (₀ , b1) lm CZ)))
      (trans (axiom selinger-c12)
      (sym (refl' (Eq.cong
          (λ pr → CZ • pr .proj₁)
          (ract-↑-≡ (₀ , b1 + - ₀)
            (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ)))))

    fix2 : ∀ (t3 : ℤ ₚ) →
      inj₂ ((₀ , b1 + - ₀) ,
        inj₂ ((₀ , (b2 + - ₀) + - ₀) , inj₂ ((₀ , t3 + - ₀) , lm3))) ≡
      inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , t3) , lm3)))
    fix2 t3 = Eq.cong₂
      (λ v w → inj₂ ((₀ , v) , w))
      (e0 b1)
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm3)))
        (Eq.trans (e0 (b2 + - ₀)) (e0 b2))
        (e0 t3))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₂
    coset≡ =
      Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
          (ract-↑-≡ (₀ , b1) lm CZ))
      (Eq.trans (fix2 b3)
      (Eq.sym (Eq.trans (Eq.cong proj₂
          (ract-↑-≡ (₀ , b1 + - ₀)
            (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ))
        (fix2 b3))))

------------------------------------------------------------------------
-- c12 with a2 = 0: the wire-2 slot is clean, and the two escapes
-- commute letterwise (with the axiom at the CZ cores).

  module _ where
    open PP ((₃₊ m) QRel,_===_)
    open SR word-setoid

    c12-go-a00 : ∀ (a1' : Fin (₁₊ p-2)) (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
      ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
        (CZ ↑ • CZ)) ≋
      ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))))
        (CZ • CZ ↑))
    c12-go-a00 a1' b1 b2 b3 lm3 = resid≈ , coset≡
      where
      lm : C (₃₊ m)
      lm = inj₂ ((₀ , b2) , inj₂ ((₀ , b3) , lm3))

      e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
      e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

      slide : CZ ↑ • (H • (CZ • H ^ 3)) ≈ (H • (CZ • H ^ 3)) • CZ ↑
      slide = begin
        CZ ↑ • (H • (CZ • H ^ 3))   ≈⟨ sym assoc ⟩
        (CZ ↑ • H) • (CZ • H ^ 3)   ≈⟨ cleft (sym (lemma-comm-H-w↑ CZ)) ⟩
        (H • CZ ↑) • (CZ • H ^ 3)   ≈⟨ assoc ⟩
        H • (CZ ↑ • (CZ • H ^ 3))   ≈⟨ cright (sym assoc) ⟩
        H • ((CZ ↑ • CZ) • H ^ 3)   ≈⟨ cright (cleft (axiom selinger-c12)) ⟩
        H • ((CZ • CZ ↑) • H ^ 3)   ≈⟨ cright assoc ⟩
        H • (CZ • (CZ ↑ • H ^ 3))
          ≈⟨ cright (cright (sym (comm⇒pow-comm {w = H} {v = CZ ↑} 3 1
               (lemma-comm-H-w↑ CZ)))) ⟩
        H • (CZ • (H ^ 3 • CZ ↑))   ≈⟨ cright (sym assoc) ⟩
        H • ((CZ • H ^ 3) • CZ ↑)   ≈⟨ sym assoc ⟩
        (H • (CZ • H ^ 3)) • CZ ↑ ∎

      resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
               ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • CZ ↑)) .proj₁
      resid≈ =
        trans (refl' (Eq.cong
            (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
            (ract-↑-≡ (₁₊ a1' , b1) lm CZ)))
        (trans slide
        (sym (refl' (Eq.cong
            (λ pr → (H • (CZ • H ^ 3)) • pr .proj₁)
            (ract-↑-≡ (₁₊ a1' , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₁₊ a1') , inj₂ ((₀ , b3) , lm3))) CZ)))))

      coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
               ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • CZ ↑)) .proj₂
      coset≡ =
        Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
            (ract-↑-≡ (₁₊ a1' , b1) lm CZ))
        (Eq.trans (Eq.cong₂
            (λ v rest → inj₂ ((₁₊ a1' , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₀ , t) , lm3)))
              (Eq.cong (_+ - ₁₊ a1') (e0 b2))
              (e0 b3)))
        (Eq.sym (Eq.trans (Eq.cong proj₂
            (ract-↑-≡ (₁₊ a1' , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₁₊ a1') , inj₂ ((₀ , b3) , lm3))) CZ))
          (Eq.cong₂
            (λ v rest → inj₂ ((₁₊ a1' , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₀ , t) , lm3)))
              (e0 (b2 + - ₁₊ a1'))
              (e0 b3))))))

    c12-go-00c : ∀ (a3' : Fin (₁₊ p-2)) (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
      ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))))
        (CZ ↑ • CZ)) ≋
      ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))))
        (CZ • CZ ↑))
    c12-go-00c a3' b1 b2 b3 lm3 = resid≈ , coset≡
      where
      lm : C (₃₊ m)
      lm = inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))

      e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
      e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

      slide : ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3)) • CZ ≈
              CZ • ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3))
      slide = begin
        ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3)) • CZ   ≈⟨ assoc ⟩
        (H ↑) ↑ • ((CZ ↑ • ((H ↑) ↑) ^ 3) • CZ)   ≈⟨ cright assoc ⟩
        (H ↑) ↑ • (CZ ↑ • (((H ↑) ↑) ^ 3 • CZ))
          ≈⟨ cright (cright (comm⇒pow-comm {w = (H ↑) ↑} {v = CZ} 3 1
               (sym (lemma-comm-CZ-w↑ H)))) ⟩
        (H ↑) ↑ • (CZ ↑ • (CZ • ((H ↑) ↑) ^ 3))   ≈⟨ cright (sym assoc) ⟩
        (H ↑) ↑ • ((CZ ↑ • CZ) • ((H ↑) ↑) ^ 3)   ≈⟨ cright (cleft (axiom selinger-c12)) ⟩
        (H ↑) ↑ • ((CZ • CZ ↑) • ((H ↑) ↑) ^ 3)   ≈⟨ cright assoc ⟩
        (H ↑) ↑ • (CZ • (CZ ↑ • ((H ↑) ↑) ^ 3))   ≈⟨ sym assoc ⟩
        ((H ↑) ↑ • CZ) • (CZ ↑ • ((H ↑) ↑) ^ 3)   ≈⟨ cleft (sym (lemma-comm-CZ-w↑ H)) ⟩
        (CZ • (H ↑) ↑) • (CZ ↑ • ((H ↑) ↑) ^ 3)   ≈⟨ assoc ⟩
        CZ • ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3)) ∎

      resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
               ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₁
      resid≈ =
        trans (refl' (Eq.cong
            (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
            (ract-↑-≡ (₀ , b1) lm CZ)))
        (trans slide
        (sym (refl' (Eq.cong
            (λ pr → CZ • pr .proj₁)
            (ract-↑-≡ (₀ , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₁₊ a3' , b3) , lm3))) CZ)))))

      coset≡ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
               ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₂
      coset≡ =
        Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
            (ract-↑-≡ (₀ , b1) lm CZ))
        (Eq.trans (Eq.cong₂
            (λ v rest → inj₂ ((₀ , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₁₊ a3' , t) , lm3)))
              (e0 (b2 + - ₁₊ a3'))
              (e0 b3)))
        (Eq.sym (Eq.trans (Eq.cong proj₂
            (ract-↑-≡ (₀ , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₀) , inj₂ ((₁₊ a3' , b3) , lm3))) CZ))
          (Eq.cong₂
            (λ v rest → inj₂ ((₀ , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₁₊ a3' , t) , lm3)))
              (Eq.cong (_+ - ₁₊ a3') (e0 b2))
              (e0 b3))))))

    private
      cpX : ∀ {X A B : Word (Gen (₃₊ m))} →
        X • A ≈ A • X → X • B ≈ B • X → X • (A • B) ≈ (A • B) • X
      cpX ca cb = trans (sym assoc)
        (trans (cong ca refl) (trans assoc (trans (cong refl cb) (sym assoc))))

      cpL : ∀ {A B Y : Word (Gen (₃₊ m))} →
        A • Y ≈ Y • A → B • Y ≈ Y • B → (A • B) • Y ≈ Y • (A • B)
      cpL ca cb = trans assoc
        (trans (cong refl cb) (trans (sym assoc) (trans (cong ca refl) assoc)))

    c12-go-a0c : ∀ (a1' a3' : Fin (₁₊ p-2)) (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
      ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))))
        (CZ ↑ • CZ)) ≋
      ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))))
        (CZ • CZ ↑))
    c12-go-a0c a1' a3' b1 b2 b3 lm3 = resid≈ , coset≡
      where
      lm : C (₃₊ m)
      lm = inj₂ ((₀ , b2) , inj₂ ((₁₊ a3' , b3) , lm3))

      e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
      e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

      Y : Word (Gen (₃₊ m))
      Y = H • (CZ • H ^ 3)

      X₁Y : (H ↑) ↑ • Y ≈ Y • (H ↑) ↑
      X₁Y = cpX (sym (lemma-comm-H-w↑ (H ↑)))
        (cpX (sym (lemma-comm-CZ-w↑ H))
          (sym (comm⇒pow-comm {w = H} {v = (H ↑) ↑} 3 1
            (lemma-comm-H-w↑ (H ↑)))))

      X₂Y : CZ ↑ • Y ≈ Y • CZ ↑
      X₂Y = cpX (sym (lemma-comm-H-w↑ CZ))
        (cpX (axiom selinger-c12)
          (sym (comm⇒pow-comm {w = H} {v = CZ ↑} 3 1
            (lemma-comm-H-w↑ CZ))))

      X₃Y : ((H ↑) ↑) ^ 3 • Y ≈ Y • ((H ↑) ↑) ^ 3
      X₃Y = cpX (comm⇒pow-comm {w = (H ↑) ↑} {v = H} 3 1
              (sym (lemma-comm-H-w↑ (H ↑))))
        (cpX (comm⇒pow-comm {w = (H ↑) ↑} {v = CZ} 3 1
              (sym (lemma-comm-CZ-w↑ H)))
          (comm⇒pow-comm {w = (H ↑) ↑} {v = H} 3 3
            (sym (lemma-comm-H-w↑ (H ↑)))))

      slide : ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3)) • Y ≈
              Y • ((H ↑) ↑ • (CZ ↑ • ((H ↑) ↑) ^ 3))
      slide = cpL X₁Y (cpL X₂Y X₃Y)

      resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
               ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • CZ ↑)) .proj₁
      resid≈ =
        trans (refl' (Eq.cong
            (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
            (ract-↑-≡ (₁₊ a1' , b1) lm CZ)))
        (trans slide
        (sym (refl' (Eq.cong
            (λ pr → Y • pr .proj₁)
            (ract-↑-≡ (₁₊ a1' , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₁₊ a1') , inj₂ ((₁₊ a3' , b3) , lm3))) CZ)))))

      coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
               ((ract3 ᵗ) (inj₂ ((₁₊ a1' , b1) , lm)) (CZ • CZ ↑)) .proj₂
      coset≡ =
        Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
            (ract-↑-≡ (₁₊ a1' , b1) lm CZ))
        (Eq.trans (Eq.cong₂
            (λ v rest → inj₂ ((₁₊ a1' , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₁₊ a3' , t) , lm3)))
              (sub-swap b2 (₁₊ a3') (₁₊ a1'))
              (e0 b3)))
        (Eq.sym (Eq.trans (Eq.cong proj₂
            (ract-↑-≡ (₁₊ a1' , b1 + - ₀)
              (inj₂ ((₀ , b2 + - ₁₊ a1') , inj₂ ((₁₊ a3' , b3) , lm3))) CZ))
          (Eq.cong₂
            (λ v rest → inj₂ ((₁₊ a1' , v) , rest))
            (e0 b1)
            (Eq.cong₂ (λ w t → inj₂ ((₀ , w) , inj₂ ((₁₊ a3' , t) , lm3)))
              Eq.refl
              (e0 b3))))))

------------------------------------------------------------------------
-- c12 with a nonzero middle wire: both escapes are conjugated by the
-- same H↑, so the conjugations merge and the axiom applies inside.

    conj-merge : ∀ (X Y : Word (Gen (₃₊ m))) →
      (H ↑ • (X • (H ↑) ^ 3)) • (H ↑ • (Y • (H ↑) ^ 3)) ≈
      H ↑ • ((X • Y) • (H ↑) ^ 3)
    conj-merge X Y = begin
      (H ↑ • (X • (H ↑) ^ 3)) • (H ↑ • (Y • (H ↑) ^ 3))   ≈⟨ assoc ⟩
      H ↑ • ((X • (H ↑) ^ 3) • (H ↑ • (Y • (H ↑) ^ 3)))   ≈⟨ cright assoc ⟩
      H ↑ • (X • ((H ↑) ^ 3 • (H ↑ • (Y • (H ↑) ^ 3))))   ≈⟨ cright (cright (sym assoc)) ⟩
      H ↑ • (X • (((H ↑) ^ 3 • H ↑) • (Y • (H ↑) ^ 3)))   ≈⟨ cright (cright (cleft (H↑3H↑≈ε {₁₊ m}))) ⟩
      H ↑ • (X • (ε • (Y • (H ↑) ^ 3)))                   ≈⟨ cright (cright left-unit) ⟩
      H ↑ • (X • (Y • (H ↑) ^ 3))                         ≈⟨ cright (sym assoc) ⟩
      H ↑ • ((X • Y) • (H ↑) ^ 3) ∎

    c12-go-0c0 : ∀ (a2' : Fin (₁₊ p-2)) (b1 b2 b3 : ℤ ₚ) (lm3 : C (₁₊ m)) →
      ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₀ , b3) , lm3))))
        (CZ ↑ • CZ)) ≋
      ((ract3 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , b2) , inj₂ ((₀ , b3) , lm3))))
        (CZ • CZ ↑))
    c12-go-0c0 a2' b1 b2 b3 lm3 = resid≈ , coset≡
      where
      lm : C (₃₊ m)
      lm = inj₂ ((₁₊ a2' , b2) , inj₂ ((₀ , b3) , lm3))

      e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
      e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

      slide : (H ↑ • (CZ ↑ • (H ↑) ^ 3)) • (H ↑ • (CZ • (H ↑) ^ 3)) ≈
              (H ↑ • (CZ • (H ↑) ^ 3)) • (H ↑ • (CZ ↑ • (H ↑) ^ 3))
      slide =
        trans (conj-merge (CZ ↑) CZ)
        (trans (cright (cleft (axiom selinger-c12)))
               (sym (conj-merge CZ (CZ ↑))))

      resid≈ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₁ ≈
               ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₁
      resid≈ =
        trans (refl' (Eq.cong
            (λ pr → pr .proj₁ • ((ract3 ᵗ) (pr .proj₂) CZ) .proj₁)
            (ract-↑-≡ (₀ , b1) lm CZ)))
        (trans slide
        (sym (refl' (Eq.cong
            (λ pr → (H ↑ • (CZ • (H ↑) ^ 3)) • pr .proj₁)
            (ract-↑-≡ (₀ , b1 + - ₁₊ a2')
              (inj₂ ((₁₊ a2' , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ)))))

      coset≡ : ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ ↑ • CZ)) .proj₂ ≡
               ((ract3 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • CZ ↑)) .proj₂
      coset≡ =
        Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) (pr .proj₂) CZ) .proj₂)
            (ract-↑-≡ (₀ , b1) lm CZ))
        (Eq.trans (Eq.cong
            (λ w → inj₂ ((₀ , b1 + - ₁₊ a2') ,
              inj₂ ((₁₊ a2' , w) , inj₂ ((₀ , b3 + - ₁₊ a2') , lm3))))
            (Eq.trans (e0 (b2 + - ₀)) (e0 b2)))
        (Eq.sym (Eq.trans (Eq.cong proj₂
            (ract-↑-≡ (₀ , b1 + - ₁₊ a2')
              (inj₂ ((₁₊ a2' , b2 + - ₀) , inj₂ ((₀ , b3) , lm3))) CZ))
          (Eq.cong
            (λ w → inj₂ ((₀ , b1 + - ₁₊ a2') ,
              inj₂ ((₁₊ a2' , w) , inj₂ ((₀ , b3 + - ₁₊ a2') , lm3))))
            (Eq.trans (e0 (b2 + - ₀)) (e0 b2))))))
