{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02833 as MV02833
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02834 as MV02834
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K0126 ≈ M0 • K0126 • M0 • K0126 • M0
proved = GL.•-cancelʳ {g = X12 • K0126} {g' = M0 • K0126 • M0 • K0126 • M0} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV02833.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV02834.proved (move-product MV00643.proved (move-product MV02834.proved (move-product MV00643.proved (MV02834.proved)))))))
