{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02835 as MV02835
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02836 as MV02836
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K0127 ≈ M0 • K0127 • M0 • K0127 • M0
proved = GL.•-cancelʳ {g = X12 • K0127} {g' = M0 • K0127 • M0 • K0127 • M0} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02835.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV02836.proved (move-product MV00644.proved (move-product MV02836.proved (move-product MV00644.proved (MV02836.proved)))))))
