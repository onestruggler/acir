{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01151 as MV01151
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01152 as MV01152
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K1235 ≈ K1235 • X06
proved = GL.•-cancelʳ {g = X06 • K1235} {g' = K1235 • X06} {h = p (s0 • s1 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01151.proved (MV01152.proved))) (trans (cong refl Base.proved) (move-product MV01152.proved (MV01151.proved))))
