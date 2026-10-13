{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02854 as MV02854
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02855 as MV02855
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K0167 ≈ M0 • K0167 • M0 • K0167 • M0
proved = GL.•-cancelʳ {g = X16 • K0167} {g' = M0 • K0167 • M0 • K0167 • M0} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02854.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV02855.proved (move-product MV00654.proved (move-product MV02855.proved (move-product MV00654.proved (MV02855.proved)))))))
