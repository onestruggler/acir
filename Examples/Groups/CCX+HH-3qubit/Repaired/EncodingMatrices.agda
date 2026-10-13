{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.EncodingMatrices where

open import Data.Fin.Base using (zero ; suc)
open import Data.Product.Base using (_,_ )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.CCX+HH-3qubit.Core
open import Examples.Groups.CCX+HH-3qubit.Matrix using (module BM ; ⟦_⟧ᴹ ; matrix-gen ; matrix-ε ; matrix-• ; matrix-sound)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding using (encode ; e)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS

module Dim = SS.Dim 4

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_ SS.actV SS.set₁ SS.set₂

  primitive-matrix : ∀ g → Dim.⟦ encode g ⟧ᴸ ≡ BM.Φ (degree (embed g) , ix (gateM (embed g)))
  primitive-matrix cX0 = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cCX01 = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cCCX12 = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cK12 = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cCCZ = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cNK = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
  primitive-matrix cH2 = SS.mat-ext
    (λ { (zero) (zero) → Eq.refl
       ; (zero) (suc (zero)) → Eq.refl
       ; (zero) (suc (suc (zero))) → Eq.refl
       ; (zero) (suc (suc (suc (zero)))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (zero)) (zero) → Eq.refl
       ; (suc (zero)) (suc (zero)) → Eq.refl
       ; (suc (zero)) (suc (suc (zero))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (zero))) (zero) → Eq.refl
       ; (suc (suc (zero))) (suc (zero)) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (zero) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl
       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _
       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

core-matrix : ∀ w → Dim.⟦ (encode ʷ) w ⟧ᴸ ≡ ⟦ ⌞ w ⌟ ⟧ᴹ
core-matrix [ g ]ʷ = Eq.trans (primitive-matrix g) (Eq.sym (matrix-gen (embed g)))
core-matrix ε = Eq.sym matrix-ε
core-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ ((encode ʷ) w) ((encode ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (core-matrix w) (core-matrix v))
    (Eq.sym (matrix-• ⌞ w ⌟ ⌞ v ⌟)))

gen-matrix : ∀ g → Dim.⟦ e g ⟧ᴸ ≡ ⟦ [ g ]ʷ ⟧ᴹ
gen-matrix g = Eq.trans (core-matrix (core g)) (Eq.sym (matrix-sound (gen-expand g)))

-- The encoding denotes exactly the same matrix as the circuit.
encode-matrix : ∀ w → Dim.⟦ (e ʷ) w ⟧ᴸ ≡ ⟦ w ⟧ᴹ
encode-matrix [ g ]ʷ = gen-matrix g
encode-matrix ε = Eq.sym matrix-ε
encode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ ((e ʷ) w) ((e ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (encode-matrix w) (encode-matrix v))
    (Eq.sym (matrix-• w v)))
