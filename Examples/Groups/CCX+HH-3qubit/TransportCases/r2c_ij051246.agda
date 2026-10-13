{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01125 as MV01125
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01126 as MV01126
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • K1246 ≈ K1246 • X05
proved = GL.•-cancelʳ {g = X05 • K1246} {g' = K1246 • X05} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01125.proved (MV01126.proved))) (trans (cong refl Base.proved) (move-product MV01126.proved (MV01125.proved))))
