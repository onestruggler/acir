{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X12 where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
open import Data.Product.Base using (_,_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.CCX+HH-3qubit.Interpretation
import Examples.Groups.CCX+HH-3qubit.FrameWords as F
open import Examples.Groups.CCX+HH-3qubit.Matrix using (module BM ; ⟦_⟧ᴹ)
open import Examples.Groups.CCX+HH-3qubit.FrameEvaluation using (matrix23 ; e23)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
module Dim = SS.Dim 4

letter : T.Gen 8
letter = T.X-gen (suc (zero)) (suc (suc (zero))) (s≤s (s≤s z≤n))

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_ SS.actV SS.set₁ SS.set₂
  calculation : Dim.⟦ [ L.⌊ letter ⌋ ]ʷ ⟧ᴸ ≡ BM.Φ (0 , ix matrix23)
  calculation = SS.mat-ext (λ { (zero) (zero) → Eq.refl
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

proved : Dim.⟦ [ L.⌊ letter ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.X12 ⟧ᴹ
proved = Eq.trans calculation (Eq.sym
  (BM.Φ-≐ {ℓ = 0} {M = ix (readM F.X12)} {M′ = ix matrix23}
    (λ x y → Eq.cong (λ M → ix M x y) e23)))
