------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of λ⁰: the control on wire 4, where it reads 0
--
-- λ⁰ of a four-wire circuit w denotes ctrl ⟦ w ⟧ (`Λ⁰-sem`): on a
-- generator by evaluation (Five.Sem.LamEval1, LamEval2), on a product by
-- the multiplicativity of ctrl (Five.Sem.TL), λ⁰ being a homomorphism up
-- to the sound five-wire theory.  `ctrl-cong`: the control respects the
-- scaled equivalence.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List ; [] ; _∷_)
open import Word.Base using (ε)
open import Examples.Groups.Clifford+CS.Five.Chain
  using (⟪_⟫ʷ ; _≈_ ; X4)
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ)

module Examples.Groups.Clifford+CS.Five.Sem.Lam
  (F4ᵍ : ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ)
  (F5ᵍ : ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ)
  (x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε)
  where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Vec as V
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; _•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
  using (Gen ; Circuit ; gate₀ ; gate₁ ; gate₂ ; _↥ ; I-gate ; S-gate ; K-gate ; CS-gate)
open import Examples.Groups.Clifford+CS.Interpretation
  using (⟦_⟧ ; ⟦_⟧ᵍ ; ⟦_⟧ₒ ; ⟦⟧ₒ-gen ; ⟦⟧ₒ-ε ; ⟦⟧ₒ-• ; len)
open import Examples.Groups.Clifford+CS.Five.Soundness using (soundₓ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL
  using (ctrl ; ctrlOp ; ctrl-∙ ; ctrl-ε ; P₀ ; P₁ ; γI)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.LamEval1
open import Examples.Groups.Clifford+CS.Five.Sem.LamEval2
import Examples.Groups.Clifford+CS.Five.Calc as Calc

open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰ ; hom⁰)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- The control and the scaled equivalence

private
  tensor-scale : (c : 𝔽) (M : Op m) (N : Op n) → ∀ x y → c * tensor M N x y ≡ tensor (c · M) N x y
  tensor-scale {zero}  c M N x       y       = Eq.sym (*-assoc c (M V.[] V.[]) (N x y))
  tensor-scale {suc m} c M N (a V.∷ x) (b V.∷ y) =
    tensor-scale {m} c (λ u v → M (a V.∷ u) (b V.∷ v)) N x y

ctrl-cong : {s t : Scaled m} → s ~ t → ctrl s ~ ctrl t
ctrl-cong {m} {k , M} {l , N} e x y =
  Eq.trans (*-distribˡ-+ (γ^ l) (tensor M P₀ x y) (tensor (γI {m} k) P₁ x y))
    (Eq.trans (Eq.cong₂ _+_ A B)
      (Eq.sym (*-distribˡ-+ (γ^ k) (tensor N P₀ x y) (tensor (γI {m} l) P₁ x y))))
  where
  A : γ^ l * tensor M P₀ x y ≡ γ^ k * tensor N P₀ x y
  A = Eq.trans (tensor-scale (γ^ l) M P₀ x y)
        (Eq.trans (tensor-cong {M = γ^ l · M} {M' = γ^ k · N} e (≐-refl P₀) x y)
          (Eq.sym (tensor-scale (γ^ k) N P₀ x y)))

  B : γ^ l * tensor (γI {m} k) P₁ x y ≡ γ^ k * tensor (γI {m} l) P₁ x y
  B = Eq.trans (tensor-scale (γ^ l) (γI k) P₁ x y)
        (Eq.trans (tensor-cong {M = γ^ l · γI {m} k} {M' = γ^ k · γI {m} l}
                     (·-comm (γ^ l) (γ^ k) Idₒ) (≐-refl P₁) x y)
          (Eq.sym (tensor-scale (γ^ k) (γI l) P₁ x y)))

-- At one scale, pointwise equal operators.
ctrl-≐ : ∀ {k} {M M′ : Op m} → M ≐ M′ → ctrl (k , M) ~ ctrl (k , M′)
ctrl-≐ {m} {k} {M} {M′} e = ctrl-cong {m} {k , M} {k , M′} (·-cong Eq.refl e)

------------------------------------------------------------------------
-- λ⁰ on generators

private
  lam : (g : Gen 4) → ⟦ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ ⟧ ~ (1 , ctrlOp {4} 1 ⟦ g ⟧ᵍ)
  lam (gate₀ I-gate)                = lam-I
  lam (gate₁ S-gate)                = lam-S
  lam (gate₁ K-gate)                = lam-K
  lam (gate₂ CS-gate)               = lam-CS
  lam (gate₀ I-gate ↥)              = lam-I↑
  lam (gate₁ S-gate ↥)              = lam-S↑
  lam (gate₁ K-gate ↥)              = lam-K↑
  lam (gate₂ CS-gate ↥)             = lam-CS↑
  lam (gate₀ I-gate ↥ ↥)            = lam-I↑↑
  lam (gate₁ S-gate ↥ ↥)            = lam-S↑↑
  lam (gate₁ K-gate ↥ ↥)            = lam-K↑↑
  lam (gate₂ CS-gate ↥ ↥)           = lam-CS↑↑
  lam (gate₀ I-gate ↥ ↥ ↥)          = lam-I↑↑↑
  lam (gate₁ S-gate ↥ ↥ ↥)          = lam-S↑↑↑
  lam (gate₁ K-gate ↥ ↥ ↥)          = lam-K↑↑↑
  lam (gate₀ I-gate ↥ ↥ ↥ ↥)        = lam-I↑↑↑↑

------------------------------------------------------------------------
-- λ⁰ on words

Λ⁰-sem : (w : Circuit 4) → ⟦ Λ⁰ w ⟧ ~ ctrl ⟦ w ⟧
Λ⁰-sem [ g ]ʷ =
  ~-trans {s = ⟦ Λ⁰ [ g ]ʷ ⟧} {t = 1 , ctrlOp {4} 1 ⟦ g ⟧ᵍ} {u = ctrl ⟦ [ g ]ʷ ⟧}
    (lam g) (ctrl-≐ {4} {1} {⟦ g ⟧ᵍ} {⟦ [ g ]ʷ ⟧ₒ} (≐-sym (⟦⟧ₒ-gen g)))
Λ⁰-sem ε =
  ~-trans {s = ⟦_⟧ {5} ε} {t = ε∙} {u = ctrl (⟦_⟧ {4} ε)}
    (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {5} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
    (~-trans {s = ε∙} {t = ctrl (ε∙ {4})} {u = ctrl (⟦_⟧ {4} ε)}
      (~-sym {s = ctrl (ε∙ {4})} {t = ε∙} (ctrl-ε {4}))
      (ctrl-≐ {4} {0} {Idₒ} {⟦_⟧ₒ {4} ε} (≐-sym ⟦⟧ₒ-ε)))
Λ⁰-sem (u • v) =
  ~-trans {s = ⟦ Λ⁰ (u • v) ⟧} {t = ⟦ Λ⁰ u • Λ⁰ v ⟧} {u = ctrl ⟦ u • v ⟧}
    (soundₓ (hom⁰ u v))
    (~-trans {s = ⟦ Λ⁰ u • Λ⁰ v ⟧} {t = ⟦ Λ⁰ u ⟧ ∙ ⟦ Λ⁰ v ⟧} {u = ctrl ⟦ u • v ⟧}
      (hom (Λ⁰ u) (Λ⁰ v))
      (~-trans {s = ⟦ Λ⁰ u ⟧ ∙ ⟦ Λ⁰ v ⟧} {t = ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧} {u = ctrl ⟦ u • v ⟧}
        (∙-cong {s = ⟦ Λ⁰ u ⟧} {s' = ctrl ⟦ u ⟧} {t = ⟦ Λ⁰ v ⟧} {t' = ctrl ⟦ v ⟧}
          (Λ⁰-sem u) (Λ⁰-sem v))
        (~-trans {s = ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧} {t = ctrl (⟦ u ⟧ ∙ ⟦ v ⟧)} {u = ctrl ⟦ u • v ⟧}
          (~-sym {s = ctrl (⟦ u ⟧ ∙ ⟦ v ⟧)} {t = ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧} (ctrl-∙ ⟦ u ⟧ ⟦ v ⟧))
          (ctrl-≐ {4} {len u +ℕ len v} {⟦ u ⟧ₒ ⊙ ⟦ v ⟧ₒ} {⟦ u • v ⟧ₒ} (≐-sym (⟦⟧ₒ-• u v))))))
