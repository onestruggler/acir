------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on (₁₊a1',b1)/(₁₊a2',b2), sub-case αα: both shifted
-- slots vanish (b₂ ≡ a₁ ≡ -a₂), so the first pad's S-slots take the
-- value 1 and both middle escapes are HH/H; the identity closes by the
-- axiom after H↑⁵- and H⁴-cancellations and disjoint-wire commutation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10j
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
  using (-0#≈0# ; -‿involutive)

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
  p-2 p-prime using (Sp-1-S ; SupSinv ; H5lift)
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

    PAD1c : Word (Gen (₂₊ m))
    PAD1c = H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑) ^ 3)))))

    fixdownJ : S⁻¹ {m} ↑ •
        (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
      S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdownJ = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

    H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
    H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

  idαα : PAD1c • ((H ↑ • H ↑) • WD) ≈
         (H ↑ • H ↑) • (S⁻¹ ↑ • (WD • (H ↑ • S⁻¹ ↑)))
  idαα = begin
    PAD1c • ((H ↑ • H ↑) • WD)
      ≈⟨ trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
           (trans (cright (cright (cright assoc)))
           (trans (cright (cright (cright (cright assoc))))
             (cright (cright (cright (cright (cright assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ •
      ((H ↑) ^ 3 • ((H ↑ • H ↑) • WD)))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (sym assoc) (cleft H5lift))))))) ⟩
    H • (H ↑ • (CZ • (S • (H ^ 3 • (S ↑ • (H ↑ • WD))))))
      ≈⟨ cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (H3W S)) (trans assoc (cright
             (trans (sym assoc) (trans (cleft (H3W H)) assoc))))))))) ⟩
    H • (H ↑ • (CZ • (S • (S ↑ • (H ↑ • (H ^ 3 • WD))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans assoc (trans (cright assoc)
           (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (axiom order-H)) left-unit)))))))))))  ⟩
    H • (H ↑ • (CZ • (S • (S ↑ • (H ↑ • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (lemma-comm-S-w↑ S))
           (trans assoc (cright (trans (sym assoc)
             (trans (cleft (lemma-comm-S-w↑ H)) assoc)))))))) ⟩
    H • (H ↑ • (CZ • (S ↑ • (H ↑ • (S • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (axiom comm-CZ-S↓))) assoc)))))) ⟩
    H • (H ↑ • (CZ • (S ↑ • (H ↑ • (CZ • (S • H ^ 3))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (axiom comm-CZ-S↑)) assoc))) ⟩
    H • (H ↑ • (S ↑ • (CZ • (H ↑ • (CZ • (S • H ^ 3))))))
      ≈⟨ cright (cright (cright (trans (cright (sym assoc))
           (trans (sym assoc) (trans (cleft (axiom selinger-c10))
             (cleft (refl' fixdownJ))))))) ⟩
    H • (H ↑ • (S ↑ • ((S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ •
      (H ↑ • (S⁻¹ ↑ • S⁻¹)))))) • (S • H ^ 3))))
      ≈⟨ cright (cright (trans (sym assoc) (trans (cleft
           (trans (sym assoc) (trans (cleft SupSinv) left-unit)))
           assoc))) ⟩
    H • (H ↑ • (H ↑ • ((S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))) •
      (S • H ^ 3))))
      ≈⟨ cright (cright (cright (trans assoc (trans (cright assoc)
           (trans (cright (cright assoc))
             (cright (cright (cright assoc)))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ •
      (S⁻¹ • (S • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright (cright
           (trans (sym assoc)
             (trans (cleft (Sp-1-S {₁₊ m})) left-unit)))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • H ^ 3))))))
      ≈⟨ cright (cright (cright (cright (cright
           (trans (cright (sym (H3W S⁻¹))) (trans (sym assoc)
             (trans (cleft (sym (H3W H))) assoc))))))) ⟩
    H • (H ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ trans (sym assoc) (trans (cleft (lemma-comm-H-w↑ H)) assoc) ⟩
    H ↑ • (H • (H ↑ • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ H)) assoc)) ⟩
    H ↑ • (H ↑ • (H • (S⁻¹ ↑ • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ cright (cright (trans (sym assoc)
           (trans (cleft (lemma-comm-H-w↑ S⁻¹)) assoc))) ⟩
    H ↑ • (H ↑ • (S⁻¹ ↑ • (H • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑))))))
      ≈⟨ sym assoc ⟩
    (H ↑ • H ↑) • (S⁻¹ ↑ • (H • (CZ • (H ^ 3 • (H ↑ • S⁻¹ ↑)))))
      ≈⟨ cright (cright (trans (cright (sym assoc)) (sym assoc))) ⟩
    (H ↑ • H ↑) • (S⁻¹ ↑ • (WD • (H ↑ • S⁻¹ ↑))) ∎
