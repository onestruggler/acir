------------------------------------------------------------------------
-- Presentations of groups
--
-- The retained defining relation is sound for the intended matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.Soundness where

open import Data.Product.Base using (_,_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.CCX+HH-3qubit.Interpretation
import Examples.Groups.CCX+HH-3qubit.Soundness as Original
import Examples.Groups.CCX+HH-3qubit.Repaired.KMatrix as K
import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S
import Normalization.StarInterp as SI

axiom-sound : ∀ {w v} → w === v → ⟦ w ⟧ ~ ⟦ v ⟧
axiom-sound (paper e) = Original.axiom-sound e
axiom-sound K-definition = by-matrix K.checked

module New = SI.Extend _===_ (Scaled-monoid 3)
  (λ g → degree g , ix (gateM g))

-- New.⟦_⟧ and Ext.⟦_⟧ have the same generator interpretation;
-- only the relation indexing the soundness builder changes.
private
  axiom-sound′ : ∀ {w v} → w === v → New.⟦ w ⟧ ~ New.⟦ v ⟧
  axiom-sound′ {w} {v} e = S.~-trans
    {s = New.⟦ w ⟧} {t = ⟦ w ⟧} {u = New.⟦ v ⟧}
    (S.~-sym {s = ⟦ w ⟧} {t = New.⟦ w ⟧} (⟦⟧-Ext w))
    (S.~-trans {s = ⟦ w ⟧} {t = ⟦ v ⟧} {u = New.⟦ v ⟧}
      (axiom-sound e) (⟦⟧-Ext v))
  module Cong = New.Cong axiom-sound′

sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
sound {w} {v} e = S.~-trans
  {s = ⟦ w ⟧} {t = New.⟦ w ⟧} {u = ⟦ v ⟧} (⟦⟧-Ext w)
  (S.~-trans {s = New.⟦ w ⟧} {t = New.⟦ v ⟧} {u = ⟦ v ⟧}
    (Cong.fʷ-cong e)
    (S.~-sym {s = ⟦ v ⟧} {t = New.⟦ v ⟧} (⟦⟧-Ext v)))
