{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01157 as MV01157
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01158 as MV01158
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K1247 ≈ K1247 • X06
proved = GL.•-cancelʳ {g = X06 • K1247} {g' = K1247 • X06} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01157.proved (MV01158.proved))) (trans (cong refl Base.proved) (move-product MV01158.proved (MV01157.proved))))
