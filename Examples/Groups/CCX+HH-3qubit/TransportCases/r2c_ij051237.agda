{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij051237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01123 as MV01123
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01124 as MV01124
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • K1237 ≈ K1237 • X05
proved = GL.•-cancelʳ {g = X05 • K1237} {g' = K1237 • X05} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01123.proved (MV01124.proved))) (trans (cong refl Base.proved) (move-product MV01124.proved (MV01123.proved))))
