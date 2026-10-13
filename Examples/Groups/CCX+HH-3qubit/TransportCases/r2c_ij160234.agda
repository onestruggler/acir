{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01309 as MV01309
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01310 as MV01310
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K0234 ≈ K0234 • X16
proved = GL.•-cancelʳ {g = X16 • K0234} {g' = K0234 • X16} {h = p (s1 • s2 • s3 • s5)}
  (trans (sym (move-product MV01309.proved (MV01310.proved))) (trans (cong refl Base.proved) (move-product MV01310.proved (MV01309.proved))))
