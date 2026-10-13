{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02879 as MV02879
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02880 as MV02880
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K0347 ≈ M0 • K0347 • M0 • K0347 • M0
proved = GL.•-cancelʳ {g = X34 • K0347} {g' = M0 • K0347 • M0 • K0347 • M0} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02879.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV02880.proved (move-product MV00667.proved (move-product MV02880.proved (move-product MV00667.proved (MV02880.proved)))))))
