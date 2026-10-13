{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02600 as MV02600
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02974 as MV02974
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0156 ≈ K0156 • X16
proved = GL.•-cancelʳ {g = X56 • K0156} {g' = K0156 • X16} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02974.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV02600.proved))))
