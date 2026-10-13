{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01393 as MV01393
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0135 ≈ K0135 • X24
proved = GL.•-cancelʳ {g = X24 • K0135} {g' = K0135 • X24} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV01393.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV01393.proved))))
