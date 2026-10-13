{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01127 as MV01127
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01128 as MV01128
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • K1247 ≈ K1247 • X05
proved = GL.•-cancelʳ {g = X05 • K1247} {g' = K1247 • X05} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01127.proved (MV01128.proved))) (trans (cong refl Base.proved) (move-product MV01128.proved (MV01127.proved))))
