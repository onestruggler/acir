{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01311 as MV01311
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01312 as MV01312
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K0235 ≈ K0235 • X16
proved = GL.•-cancelʳ {g = X16 • K0235} {g' = K0235 • X16} {h = p (s1 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01311.proved (MV01312.proved))) (trans (cong refl Base.proved) (move-product MV01312.proved (MV01311.proved))))
