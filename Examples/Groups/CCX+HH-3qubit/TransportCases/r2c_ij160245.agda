{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01315 as MV01315
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01316 as MV01316
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K0245 ≈ K0245 • X16
proved = GL.•-cancelʳ {g = X16 • K0245} {g' = K0245 • X16} {h = p (s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01315.proved (MV01316.proved))) (trans (cong refl Base.proved) (move-product MV01316.proved (MV01315.proved))))
