------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of λ¹: the control on wire 4, where it reads 1
--
-- λ¹ of a four-wire circuit (Five.Lambda.λc, letter by letter) denotes
-- ctrl₁ ⟦ w ⟧ (`λc-sem`): on a generator by evaluation (Five.Sem.
-- Lam1Eval1, Lam1Eval2), on a product by the multiplicativity of ctrl₁
-- (Five.Sem.Ctrl1), λc being a homomorphism of words by definition.
-- The soundness of the five-wire rules λ(lf), λ(hyb-sq), λ(hyb-yb)
-- follows from that of lf, hyb-sq, hyb-yb.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Lam1 where

open import Data.Nat using () renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
  using (Gen ; Circuit ; gate₀ ; gate₁ ; gate₂ ; _↥ ; I-gate ; S-gate ; K-gate ; CS-gate)
open import Examples.Groups.Clifford+CS.Interpretation
  using (⟦_⟧ ; ⟦_⟧ᵍ ; ⟦_⟧ₒ ; ⟦⟧ₒ-gen ; ⟦⟧ₒ-ε ; ⟦⟧ₒ-• ; len)
open import Examples.Groups.Clifford+CS.Five.Letters using (⟪_⟫)
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λc)
open import Examples.Groups.Clifford+CS.Five.Sem.Ctrl1
  using (ctrl₁ ; ctrl₁Op ; ctrl₁-∙ ; ctrl₁-ε ; ctrl₁-cong ; ctrl₁-≐)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Lam1Eval1
open import Examples.Groups.Clifford+CS.Five.Sem.Lam1Eval2

------------------------------------------------------------------------
-- On generators

private
  lam : (g : Gen 4) → ⟦ ⟪ λ₁ g ⟫ ⟧ ~ (1 , ctrl₁Op {4} 1 ⟦ g ⟧ᵍ)
  lam (gate₀ I-gate)                = lam1-I
  lam (gate₁ S-gate)                = lam1-S
  lam (gate₁ K-gate)                = lam1-K
  lam (gate₂ CS-gate)               = lam1-CS
  lam (gate₀ I-gate ↥)              = lam1-I↑
  lam (gate₁ S-gate ↥)              = lam1-S↑
  lam (gate₁ K-gate ↥)              = lam1-K↑
  lam (gate₂ CS-gate ↥)             = lam1-CS↑
  lam (gate₀ I-gate ↥ ↥)            = lam1-I↑↑
  lam (gate₁ S-gate ↥ ↥)            = lam1-S↑↑
  lam (gate₁ K-gate ↥ ↥)            = lam1-K↑↑
  lam (gate₂ CS-gate ↥ ↥)           = lam1-CS↑↑
  lam (gate₀ I-gate ↥ ↥ ↥)          = lam1-I↑↑↑
  lam (gate₁ S-gate ↥ ↥ ↥)          = lam1-S↑↑↑
  lam (gate₁ K-gate ↥ ↥ ↥)          = lam1-K↑↑↑
  lam (gate₀ I-gate ↥ ↥ ↥ ↥)        = lam1-I↑↑↑↑

------------------------------------------------------------------------
-- On words

λc-sem : (w : Circuit 4) → ⟦ λc w ⟧ ~ ctrl₁ ⟦ w ⟧
λc-sem [ g ]ʷ =
  ~-trans {s = ⟦ λc [ g ]ʷ ⟧} {t = 1 , ctrl₁Op {4} 1 ⟦ g ⟧ᵍ} {u = ctrl₁ ⟦ [ g ]ʷ ⟧}
    (lam g) (ctrl₁-≐ {4} {1} {⟦ g ⟧ᵍ} {⟦ [ g ]ʷ ⟧ₒ} (≐-sym (⟦⟧ₒ-gen g)))
λc-sem ε =
  ~-trans {s = ⟦_⟧ {5} ε} {t = ε∙} {u = ctrl₁ (⟦_⟧ {4} ε)}
    (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {5} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
    (~-trans {s = ε∙} {t = ctrl₁ (ε∙ {4})} {u = ctrl₁ (⟦_⟧ {4} ε)}
      (~-sym {s = ctrl₁ (ε∙ {4})} {t = ε∙} (ctrl₁-ε {4}))
      (ctrl₁-≐ {4} {0} {Idₒ} {⟦_⟧ₒ {4} ε} (≐-sym ⟦⟧ₒ-ε)))
λc-sem (u • v) =
  ~-trans {s = ⟦ λc u • λc v ⟧} {t = ⟦ λc u ⟧ ∙ ⟦ λc v ⟧} {u = ctrl₁ ⟦ u • v ⟧}
    (hom (λc u) (λc v))
    (~-trans {s = ⟦ λc u ⟧ ∙ ⟦ λc v ⟧} {t = ctrl₁ ⟦ u ⟧ ∙ ctrl₁ ⟦ v ⟧} {u = ctrl₁ ⟦ u • v ⟧}
      (∙-cong {s = ⟦ λc u ⟧} {s' = ctrl₁ ⟦ u ⟧} {t = ⟦ λc v ⟧} {t' = ctrl₁ ⟦ v ⟧}
        (λc-sem u) (λc-sem v))
      (~-trans {s = ctrl₁ ⟦ u ⟧ ∙ ctrl₁ ⟦ v ⟧} {t = ctrl₁ (⟦ u ⟧ ∙ ⟦ v ⟧)} {u = ctrl₁ ⟦ u • v ⟧}
        (~-sym {s = ctrl₁ (⟦ u ⟧ ∙ ⟦ v ⟧)} {t = ctrl₁ ⟦ u ⟧ ∙ ctrl₁ ⟦ v ⟧} (ctrl₁-∙ ⟦ u ⟧ ⟦ v ⟧))
        (ctrl₁-≐ {4} {len u +ℕ len v} {⟦ u ⟧ₒ ⊙ ⟦ v ⟧ₒ} {⟦ u • v ⟧ₒ} (≐-sym (⟦⟧ₒ-• u v)))))

-- Equal four-wire semantics give equal λ¹-images.
λc-~ : (u v : Circuit 4) → ⟦ u ⟧ ~ ⟦ v ⟧ → ⟦ λc u ⟧ ~ ⟦ λc v ⟧
λc-~ u v e =
  ~-trans {s = ⟦ λc u ⟧} {t = ctrl₁ ⟦ u ⟧} {u = ⟦ λc v ⟧} (λc-sem u)
    (~-trans {s = ctrl₁ ⟦ u ⟧} {t = ctrl₁ ⟦ v ⟧} {u = ⟦ λc v ⟧}
      (ctrl₁-cong {4} {⟦ u ⟧} {⟦ v ⟧} e)
      (~-sym {s = ⟦ λc v ⟧} {t = ctrl₁ ⟦ v ⟧} (λc-sem v)))
