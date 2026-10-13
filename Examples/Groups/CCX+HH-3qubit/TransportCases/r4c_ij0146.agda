{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0146 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00650 as MV00650
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02592 as MV02592
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02972 as MV02972
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0146 ≈ K0146 • X16
proved = GL.•-cancelʳ {g = X46 • K0146} {g' = K0146 • X16} {h = p (s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02972.proved (MV00650.proved))) (trans (cong refl Base.proved) (move-product MV00650.proved (MV02592.proved))))
