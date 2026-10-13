------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the repaired dyadic circuit rules, transferred
-- from the existing presentation of O₈(ℤ[1/2]).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DyadicCompleteness where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Normalization using (DGen ; dyadic)
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ ; module BM)
import Examples.Groups.CCX+HH-3qubit.Interpretation as I
import Examples.Groups.CCX+HH-3qubit.FrameWords as F
import Examples.Groups.CCX+HH-3qubit.TwoLevel as T
import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding as E
import Examples.Groups.CCX+HH-3qubit.Repaired.EncodingMatrices as EM
import Examples.Groups.CCX+HH-3qubit.Repaired.Soundness as Sound
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as C
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (e-injective)
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

module Dim = SS.Dim 4

matrix-sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ᴹ ≡ ⟦ v ⟧ᴹ
matrix-sound {w} {v} proof = BM.Φ-~ {I.⟦ w ⟧} {I.⟦ v ⟧} (Sound.sound proof)

private
  encoded-matrix : ∀ w → Dim.⟦ L.⌊ (E.encodeᴰ ʷ) w ⌋ʷ ⟧ᴸ ≡ ⟦ dyadic w ⟧ᴹ
  encoded-matrix w = Eq.trans
    (Eq.cong Dim.⟦_⟧ᴸ (Eq.sym (E.dyadic-encoding w)))
    (EM.encode-matrix (dyadic w))

  back : ∀ w → (F.decode ʷ) ((E.encodeᴰ ʷ) w) ≈ dyadic w
  back w = trans
    (refl' (Eq.sym (E.dyadic-decoding ((E.encodeᴰ ʷ) w))))
    (trans (refl' (Eq.cong (E.decode ʷ) (Eq.sym (E.dyadic-encoding w))))
      (E.word-back (dyadic w)))

  equality : ∀ {w v} → ⟦ dyadic w ⟧ᴹ ≡ ⟦ dyadic v ⟧ᴹ →
             S.⟦ (E.encodeᴰ ʷ) w ⟧ᵐ ≡ S.⟦ (E.encodeᴰ ʷ) v ⟧ᵐ
  equality {w} {v} eq = SS.Tr.mapM-injective e-injective
    (Eq.trans (Eq.sym (SS.⟦⌊⌋⟧ 4 ((E.encodeᴰ ʷ) w)))
      (Eq.trans (encoded-matrix w)
        (Eq.trans eq (Eq.trans (Eq.sym (encoded-matrix v))
          (SS.⟦⌊⌋⟧ 4 ((E.encodeᴰ ʷ) v))))))

completeness : ∀ {w v : Word DGen} →
               ⟦ dyadic w ⟧ᴹ ≡ ⟦ dyadic v ⟧ᴹ → dyadic w ≈ dyadic v
completeness {w} {v} eq = trans (sym (back w))
  (trans (lift (T.decode-cong
    {w = (E.encodeᴰ ʷ) w} {v = (E.encodeᴰ ʷ) v}
    (C.completeness {u = (E.encodeᴰ ʷ) w} {v = (E.encodeᴰ ʷ) v}
      (equality {w} {v} eq)))) (back v))
