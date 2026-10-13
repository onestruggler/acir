{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01779 as MV01779
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01780 as MV01780
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0135 ≈ K0135 • X67
proved = GL.•-cancelʳ {g = X67 • K0135} {g' = K0135 • X67} {h = p (s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01779.proved (MV01780.proved))) (trans (cong refl Base.proved) (move-product MV01780.proved (MV01779.proved))))
